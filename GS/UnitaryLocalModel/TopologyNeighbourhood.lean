module

public import GS.UnitaryLocalModel.TopologyFullImage
public import GS.NonmanifoldCompletion.NeighbourhoodModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# From the full compact image to a pointed neighbourhood model

This module records the inherited-topology bookkeeping. Once the actual
full-family coverage theorem supplies the source-neighbourhood assertion,
no additional local topological premise is required on either side.
-/
noncomputable section
open Matrix GS GS.UnitaryManifold Filter
open scoped Topology
namespace GS.UnitaryLocalModel

/-- View the compact image inside an ambient matrix family. -/
def fullCompactSource {q d : ℕ} (F : Set (CMat (q*2)))
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ) : Set F :=
  {M | M.val ∈ FullCompactImage ψ o r}

def fullCompactSourceHomeomorph {q d : ℕ} (F : Set (CMat (q*2)))
    (ψ : (Fin d → ℝ) → CMat q) (o : Fin q) (r : ℝ)
    (hsub : FullCompactImage ψ o r ⊆ F) :
    fullCompactSource F ψ o r ≃ₜ FullCompactImage ψ o r where
  toFun := fun x => ⟨x.val.val,x.property⟩
  invFun := fun y => ⟨⟨y.val,hsub y.property⟩,y.property⟩
  left_inv := by intro x; rfl
  right_inv := by intro y; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The bounded factor is a neighbourhood within the whole rank cone. -/
def outerConeRegion (q d : ℕ) (o : Fin q) (r : ℝ) :
    Set (OuterFactors q o × ConeCoordinates d) :=
  {p | p.2 ∈ boundedConeCoordinates d r}

def outerBoundedHomeomorph (q d : ℕ) (o : Fin q) (r : ℝ) :
    (OuterFactors q o × boundedConeCoordinates d r) ≃ₜ outerConeRegion q d o r where
  toFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
  invFun := fun p => (p.val.1,⟨p.val.2,p.property⟩)
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem outerConeRegion_mem_nhds {q d : ℕ} (o : Fin q) (r : ℝ) (hr : 0<r)
    (a : OuterFactors q o) :
    outerConeRegion q d o r ∈ 𝓝 (a,coneCoordinatesZero d) :=
  continuous_snd.continuousAt.preimage_mem_nhds (boundedConeCoordinates_mem_nhds d hr)

/-- The compact quotient produces a genuine local model once full-family
coverage and image feasibility have been established. Both subspace topologies
are the inherited ones. -/
theorem full_compact_pointed_neighbourhood_model {q d : ℕ}
    (F : Set (CMat (q*2))) (x : F) (Q : CMat q) (o : Fin q)
    (ψ : (Fin d → ℝ) → CMat q) (U : Set (Fin d → ℝ))
    (hψc : ContinuousOn ψ U) (hψi : Set.InjOn ψ U)
    (hpos : PositiveChartAnchors Q o ψ U) (r : ℝ) (hr : 0<r)
    (hargs : ∀ p ∈ localParameterBox d r, p.1+p.2.1 ∈ U ∧ p.1-p.2.1 ∈ U)
    (hsub : FullCompactImage ψ o r ⊆ F)
    (hcover : fullCompactSource F ψ o r ∈ 𝓝 x)
    (p₀ : FullCompactParameters q o d r)
    (hbase : fullCompactMiddle ψ o r p₀ = x.val)
    (hzero : parameterCone p₀.2.val = coneCoordinatesZero d) :
    Nonempty (GS.NonmanifoldCompletion.PointedNeighbourhoodModel F
      (OuterFactors q o × ConeCoordinates d) x (p₀.1,coneCoordinatesZero d)) := by
  obtain ⟨h,hh⟩ := exists_full_compact_homeomorphism Q o ψ U hψc hψi hpos r hargs
  refine ⟨{
    source := fullCompactSource F ψ o r
    target := outerConeRegion q d o r
    source_nhds := hcover
    target_nhds := outerConeRegion_mem_nhds o r hr p₀.1
    chart := ((fullCompactSourceHomeomorph F ψ o r hsub).trans h).trans
      (outerBoundedHomeomorph q d o r)
    map_point := ?_ }⟩
  intro hx
  have he : fullCompactSourceHomeomorph F ψ o r hsub ⟨x,hx⟩ =
      ⟨fullCompactMiddle ψ o r p₀,⟨p₀,rfl⟩⟩ := Subtype.ext hbase.symm
  change ((outerBoundedHomeomorph q d o r)
    (h (fullCompactSourceHomeomorph F ψ o r hsub ⟨x,hx⟩))).val = _
  rw [he,hh p₀]
  change (p₀.1,parameterCone p₀.2.val) = (p₀.1,coneCoordinatesZero d)
  rw [hzero]

end GS.UnitaryLocalModel
