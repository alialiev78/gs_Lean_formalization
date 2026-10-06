module

public import GS.NonmanifoldCompletion.NeighbourhoodModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Restrict the compact neighbourhood model to OPEN pointed neighbourhoods

The old compact images contain neighbourhoods but are not themselves open.
This file carries out the restriction rather than silently identifying these
notions. All subtype topologies remain induced. It does not supply the
homological obstruction or assert the final NonManifoldGoal.

-/
noncomputable section
open GS GS.Nonmanifold GS.NonmanifoldCompletion Filter
open scoped Topology
namespace GS.NonmanifoldObstruction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A nested subtype flattened onto its actual image. No openness is needed. -/
def flattenImage (S : Set X) (A : Set S) : A ≃ₜ (Subtype.val '' A : Set X) where
  toFun a := ⟨a.val.val, ⟨a.val,a.property,rfl⟩⟩
  invFun x := ⟨⟨x.val, by
    obtain ⟨a,ha,he⟩ := x.property
    rw [← he]
    exact a.property⟩, by
      obtain ⟨a,ha,he⟩ := x.property
      have hx : (⟨x.val, by
        rw [← he]
        exact a.property⟩ : S) = a := Subtype.ext he.symm
      simpa only [hx] using ha⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Restrict a homeomorphism to an arbitrary subset and its image. -/
def restrictImage (h : X ≃ₜ Y) (A : Set X) : A ≃ₜ (h '' A) where
  toFun x := ⟨h x.val, ⟨x.val,x.property,rfl⟩⟩
  invFun y := ⟨h.symm y.val, by
    obtain ⟨x,hx,he⟩ := y.property
    rw [← he, h.symm_apply_apply]
    exact hx⟩
  left_inv x := by apply Subtype.ext; exact h.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact h.apply_symm_apply y.val
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A relatively open subset contained in the interior is ambient-open. -/
theorem isOpen_flatten_of_subset_interior (S : Set X) (A : Set S)
    (hA : IsOpen A) (hinside : ∀ a∈A, a.val ∈ interior S) :
    IsOpen (Subtype.val '' A : Set X) := by
  let j : interior S → S := fun a => ⟨a.val, interior_subset a.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hpre : IsOpen (j ⁻¹' A) := hA.preimage hj
  have hImage : IsOpen (Subtype.val '' (j ⁻¹' A) : Set X) :=
    isOpen_interior.isOpenMap_subtype_val _ hpre
  have he : (Subtype.val '' (j ⁻¹' A) : Set X) = Subtype.val '' A := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨j a,ha,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      refine ⟨⟨a.val,hinside a ha⟩,?_,rfl⟩
      exact ha
  rw [he] at hImage
  exact hImage

structure PointedOpenModel (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) (y : Y) where
  source : Set X
  target : Set Y
  source_open : IsOpen source
  target_open : IsOpen target
  source_point : x ∈ source
  target_point : y ∈ target
  chart : source ≃ₜ target
  map_point : ∀ hx : x∈source, (chart ⟨x,hx⟩).val = y

/-- Choose a relatively open part on which BOTH ambient interiors are reached. -/
def interiorBridge {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y) :
    Set g.source :=
  {a | a.val ∈ interior g.source ∧ (g.chart a).val ∈ interior g.target}

theorem interiorBridge_open {x : X} {y : Y}
    (g : PointedNeighbourhoodModel X Y x y) : IsOpen (interiorBridge g) :=
  (isOpen_interior.preimage continuous_subtype_val).inter
    (isOpen_interior.preimage (continuous_subtype_val.comp g.chart.continuous))

/-- No compactness or manifold hypothesis is required by this germ restriction. -/
def pointedOpenModel {x : X} {y : Y} (g : PointedNeighbourhoodModel X Y x y) :
    PointedOpenModel X Y x y := by
  let A : Set g.source := interiorBridge g
  let B : Set g.target := g.chart '' A
  let U : Set X := Subtype.val '' A
  let V : Set Y := Subtype.val '' B
  have hA : IsOpen A := interiorBridge_open g
  have hB : IsOpen B := g.chart.isOpenMap A hA
  have hU : IsOpen U := isOpen_flatten_of_subset_interior g.source A hA
    (fun a ha => ha.1)
  have hV : IsOpen V := isOpen_flatten_of_subset_interior g.target B hB (by
    rintro b ⟨a,ha,rfl⟩
    exact ha.2)
  have hxS : x ∈ g.source := mem_of_mem_nhds g.source_nhds
  have hxI : x ∈ interior g.source := mem_interior_iff_mem_nhds.mpr g.source_nhds
  have hyI : y ∈ interior g.target := mem_interior_iff_mem_nhds.mpr g.target_nhds
  have hpointA : (⟨x,hxS⟩ : g.source) ∈ A := by
    refine ⟨hxI,?_⟩
    rw [g.map_point hxS]
    exact hyI
  have hxU : x ∈ U := ⟨⟨x,hxS⟩,hpointA,rfl⟩
  have hyV : y ∈ V :=
    ⟨g.chart ⟨x,hxS⟩,⟨⟨x,hxS⟩,hpointA,rfl⟩,g.map_point hxS⟩
  let h : U ≃ₜ V := ((flattenImage g.source A).symm.trans
    (restrictImage g.chart A)).trans (flattenImage g.target B)
  refine ⟨U,V,hU,hV,hxU,hyV,h,?_⟩
  intro hx
  change (g.chart ⟨x,hxS⟩).val = y
  exact g.map_point hxS

/-- The full-family model gives open local charts on each
side, still without presupposing either side to be a manifold. -/
theorem original_pointed_open_model {q : ℕ} (hq : 0<q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j≠0) :
    Nonempty (PointedOpenModel ↥(localFamily q) (ModelCoordinates q)
      (familyBase Q₀ hQ₀) (modelCoordinatesZero q)) := by
  obtain ⟨g⟩ := original_pointed_neighbourhood_model hq Q₀ hQ₀ hentries
  exact ⟨pointedOpenModel g⟩

end GS.NonmanifoldObstruction
