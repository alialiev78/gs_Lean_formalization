module

public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact equal-fibre maps

This is the topological step following the original manuscript's fibre
calculation. It requires actual compactness and continuity, not just a set
bijection. It asserts a homeomorphism, not differentiability of the image.

-/

noncomputable section
namespace GS

/-- A continuous surjection from a compact space to a Hausdorff space detects
continuity of a descended map. The proof uses closed sets directly. -/
theorem continuous_descend_compact
    {K X Y : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (f : K → X) (g : K → Y) (e : X → Y)
    (hf : Continuous f) (hg : Continuous g) (hs : Function.Surjective f)
    (he : ∀ k, e (f k) = g k) : Continuous e := by
  apply continuous_iff_isClosed.mpr
  intro s hclosed
  have hc : IsCompact (g ⁻¹' s) := (hclosed.preimage hg).isCompact
  have hset : e ⁻¹' s = f '' (g ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,rfl⟩ := hs x
      exact ⟨k, by simpa only [Set.mem_preimage, he k] using hx, rfl⟩
    · rintro ⟨k,hk,rfl⟩
      simpa only [Set.mem_preimage, he k] using hk
  rw [hset]
  exact (hc.image hf).isClosed

/-- Equal fibres give a homeomorphism which also respects the parameter maps.
The compatibility records the image of each distinguished base point. -/
theorem exists_homeomorph_ranges_of_same_fibres
    {K Y Z : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : K → Y) (g : K → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    ∃ h : Set.range f ≃ₜ Set.range g,
      ∀ k, h ⟨f k, ⟨k,rfl⟩⟩ = ⟨g k, ⟨k,rfl⟩⟩ := by
  classical
  let f' : K → Set.range f := fun k => ⟨f k, ⟨k,rfl⟩⟩
  let g' : K → Set.range g := fun k => ⟨g k, ⟨k,rfl⟩⟩
  have hf' : Continuous f' := hf.subtype_mk _
  have hg' : Continuous g' := hg.subtype_mk _
  have hsf : Function.Surjective f' := by
    rintro ⟨y,k,hk⟩
    exact ⟨k,Subtype.ext hk⟩
  have hsg : Function.Surjective g' := by
    rintro ⟨z,k,hk⟩
    exact ⟨k,Subtype.ext hk⟩
  let forward : Set.range f → Set.range g := fun y =>
    g' (Classical.choose y.property)
  let inv : Set.range g → Set.range f := fun z =>
    f' (Classical.choose z.property)
  have hto : ∀ k, forward (f' k) = g' k := by
    intro k
    apply Subtype.ext
    apply (hfg _ _).mp
    exact Classical.choose_spec (f' k).property
  have hinv : ∀ k, inv (g' k) = f' k := by
    intro k
    apply Subtype.ext
    apply (hfg _ _).mpr
    exact Classical.choose_spec (g' k).property
  have hleft : Function.LeftInverse inv forward := by
    intro y
    obtain ⟨k,rfl⟩ := hsf y
    rw [hto,hinv]
  have hright : Function.RightInverse inv forward := by
    intro z
    obtain ⟨k,rfl⟩ := hsg z
    rw [hinv,hto]
  let e : Set.range f ≃ Set.range g :=
    { toFun := forward, invFun := inv, left_inv := hleft, right_inv := hright }
  exact ⟨{
    toEquiv := e
    continuous_toFun := continuous_descend_compact f' g' forward hf' hg' hsf hto
    continuous_invFun := continuous_descend_compact g' f' inv hg' hf' hsg hinv
  }, hto⟩

/-- Equal fibres of continuous maps on a compact domain give homeomorphic
images. In particular, the maps themselves need NOT be injective. -/
theorem homeomorph_ranges_of_same_fibres
    {K Y Z : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : K → Y) (g : K → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    Nonempty (Set.range f ≃ₜ Set.range g) := by
  obtain ⟨h, _⟩ := exists_homeomorph_ranges_of_same_fibres f g hf hg hfg
  exact ⟨h⟩

end GS
