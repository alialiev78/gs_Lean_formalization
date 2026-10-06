module

public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.DephasingTopology
public import GS.UnitaryLocalModel.FactorSpace
public import GS.UnitaryLocalModel.NormalizationBaseFibre

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Continuous dephased cores on the full compact factor space

The nonzero-anchor condition cuts out an open subset of the full factor
space. Both normalized middle factors are continuous maps into the genuine
dephased unitary slice, with its inherited matrix topology.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def anchorFactorSet (Q : FullUnitary q) (o : Fin q) : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

theorem anchorFactorSet_open (Q : FullUnitary q) (o : Fin q) :
    IsOpen (anchorFactorSet Q o) := by
  exact ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))

def dephasedFirst (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.1 o)
      (dephase_unitary p.val.property.2.1 p.property.1),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.1,
        dephase_anchor_row_positive p.property.1⟩⟩

def dephasedSecond (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.2.1 o)
      (dephase_unitary p.val.property.2.2.1 p.property.2),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.2,
        dephase_anchor_row_positive p.property.2⟩⟩

@[simp] theorem dephasedFirst_val (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) :
    (dephasedFirst Q o p).val.val = dephase Q.val p.val.val.2.1 o := rfl

@[simp] theorem dephasedSecond_val (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) :
    (dephasedSecond Q o p).val.val = dephase Q.val p.val.val.2.2.1 o := rfl

theorem continuous_dephasedFirst (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedFirst Q o) := by
  have hc : Continuous (fun p : anchorFactorSet Q o => dephase Q.val p.val.val.2.1 o) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1)
      (continuousAt_dephase p.property.1) (by fun_prop)
  exact (hc.subtype_mk _).subtype_mk _

theorem continuous_dephasedSecond (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedSecond Q o) := by
  have hc : Continuous (fun p : anchorFactorSet Q o => dephase Q.val p.val.val.2.2.1 o) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1)
      (continuousAt_dephase p.property.2) (by fun_prop)
  exact (hc.subtype_mk _).subtype_mk _

/-- Every representative of the scalar base fibre satisfies the anchor condition. -/
theorem base_fibre_mem_anchorFactorSet (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : SmallFactorSpace q)
    (he : ∀ i j, p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) *
      p.val.2.2.2 j = Q.val i j • (1 : CMat 2)) : p ∈ anchorFactorSet Q o :=
  base_fibre_anchor_nonzero p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o
    p.property.1 p.property.2.2.2 (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he

theorem dephasedFirst_eq_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : anchorFactorSet Q o)
    (he : ∀ i j, p.val.val.1 i * diagTwo (p.val.val.2.1 i j) (p.val.val.2.2.1 i j) *
      p.val.val.2.2.2 j = Q.val i j • (1 : CMat 2)) :
    dephasedFirst Q o p = dephasedBase Q o hQ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (base_fibre_dephased_middle p.val.val.1 p.val.val.2.2.2 Q.val
    p.val.val.2.1 p.val.val.2.2.1 o p.val.property.1 p.val.property.2.2.2
    (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he).1

theorem dephasedSecond_eq_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : anchorFactorSet Q o)
    (he : ∀ i j, p.val.val.1 i * diagTwo (p.val.val.2.1 i j) (p.val.val.2.2.1 i j) *
      p.val.val.2.2.2 j = Q.val i j • (1 : CMat 2)) :
    dephasedSecond Q o p = dephasedBase Q o hQ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (base_fibre_dephased_middle p.val.val.1 p.val.val.2.2.2 Q.val
    p.val.val.2.1 p.val.val.2.2.1 o p.val.property.1 p.val.property.2.2.2
    (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he).2

end GS.UnitaryLocalModel
