module

public import GS.Topology.SingularHomotopyCombinatorial
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.TopCat.ToSSet

@[expose] public section

/-! # Continuous homotopies on singular simplicial sets

The prism construction is supplied by mathlib. This interface preserves the
simplicial homotopy used to construct the project's singular chain homotopy.
-/

noncomputable section
open CategoryTheory
namespace GS.Topology.SingularHomotopy

def toSimplicialHomotopy {X Y : TopCat} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    CategoryTheory.SimplicialObject.Homotopy (TopCat.toSSet.map f) (TopCat.toSSet.map g) :=
  (TopCat.Homotopy.toSSet H).toSimplicialObjectHomotopy

end GS.Topology.SingularHomotopy
