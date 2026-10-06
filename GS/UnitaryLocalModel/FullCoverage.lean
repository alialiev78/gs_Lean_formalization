module

public import GS.UnitaryLocalModel.FullCoverageCoordinates
public import GS.UnitaryLocalModel.TopologyFeasibility
public import GS.Continuation.CompactCoverageTools

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Coverage of an actual neighbourhood in the complete unitary family

Every representative of the full compact scalar-block fibre lies in the
open set where both dephased inverse coordinates are small. Exact gauge
normalization maps this open set into the compact local model. Compactness
then provides an ambient open neighbourhood whose intersection with the
original matrix family is covered. No chosen-branch coverage is assumed.
-/
noncomputable section
open Matrix GS GS.UnitaryNonmanifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

/-- Equality with the scalar-block base holds block by block in the original indexing. -/
theorem smallFactorValue_eq_base_blocks (Q : CMat q) (p : SmallFactorSpace q)
    (he : smallFactorValue q p = scalarBlockBase Q) :
    ∀ i j, p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) *
      p.val.2.2.2 j = Q i j • (1 : CMat 2) := by
  have hv : extractBlockFamily (smallFactorValue q p) = fun i j =>
      p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) * p.val.2.2.2 j := by
    funext i j a b
    exact smallFactorMap_block p.val i j a b
  have hh := congrArg (@extractBlockFamily q) he
  rw [hv,scalarBlockBase,extract_flattenBlockFamily] at hh
  intro i j
  exact congrFun (congrFun hh i) j

/-- The open coordinate set contains every representative of the complete base fibre. -/
theorem base_fibre_mem_smallFullFactors (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0<r)
    (p : SmallFactorSpace q) (he : smallFactorValue q p = scalarBlockBase Q.val) :
    p ∈ smallFullFactors Q o hQ r := by
  have hb := smallFactorValue_eq_base_blocks Q.val p he
  have ha := base_fibre_mem_anchorFactorSet Q o hQ p hb
  refine ⟨⟨p,ha⟩,?_,rfl⟩
  constructor
  · rw [dephasedFirst_eq_base Q o hQ ⟨p,ha⟩ hb]
    exact base_mem_smallDephasedSource Q o hQ r hr
  · rw [dephasedSecond_eq_base Q o hQ ⟨p,ha⟩ hb]
    exact base_mem_smallDephasedSource Q o hQ r hr

/-- Full neighbourhood coverage in the inherited ambient matrix topology. -/
theorem exists_open_full_compact_coverage (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (r : ℝ) (hr : 0<r) :
    ∃ W : Set (CMat (q*2)), IsOpen W ∧ scalarBlockBase Q.val ∈ W ∧
      ∀ M ∈ GS.UnitaryNonmanifold.localFamily q, M ∈ W →
        M ∈ FullCompactImage (euclideanDephasedParametrization Q o hQ) o r := by
  obtain ⟨W,hW,hbase,hcover⟩ := GS.Continuation.compact_full_fibre_neighbourhood
    (smallFactorValue q) (continuous_smallFactorValue q) Set.univ isCompact_univ
    (smallFullFactors Q o hQ r) (smallFullFactors_open Q o hQ r) (scalarBlockBase Q.val)
    (fun p _ he => base_fibre_mem_smallFullFactors Q o hQ r hr p he)
  refine ⟨W,hW,hbase,?_⟩
  intro M hM hMW
  have himage : M ∈ smallFactorValue q '' Set.univ := by
    rw [Set.image_univ,range_smallFactorValue]
    exact hM
  obtain ⟨p,hp,he⟩ := hcover M hMW himage
  rw [← he]
  exact smallFullFactors_map_mem Q o hQ r p hp.2

end GS.UnitaryLocalModel
