module

public import GS.Topology.SingularHomotopyChain
public import GS.Topology.SingularHomotopyPrism
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Homotopy invariance of singular homology on the pinned mathlib version

The prism triangulation constructs a simplicial homotopy of singular simplicial
sets. Applying the free-object functor and alternating-face-map construction
produces a genuine chain homotopy, which induces equal maps on homology.
No sphere-homology calculation is used.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicTopology
universe v u

namespace GS.Topology.SingularHomotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasCoproducts.{0} C] [CategoryWithHomology C]
  {X Y : TopCat} {f g : X ⟶ Y}

/-- Continuous homotopies induce chain homotopies on genuine singular chains. -/
def singularChainMapHomotopy (H : ContinuousMap.Homotopy f.hom g.hom) (R : C) :
    _root_.Homotopy (((singularChainComplexFunctor C).obj R).map f)
      (((singularChainComplexFunctor C).obj R).map g) :=
  ((toSimplicialHomotopy H).whiskerRight
    ((CategoryTheory.Limits.sigmaConst).obj R)).toChainHomotopy

/-- Homotopy invariance of singular homology, with arbitrary coefficients. -/
theorem singularHomology_map_eq (H : ContinuousMap.Homotopy f.hom g.hom) (R : C) (n : ℕ) :
    (((singularHomologyFunctor C n).obj R).map f) =
      (((singularHomologyFunctor C n).obj R).map g) :=
  (singularChainMapHomotopy H R).homologyMap_eq n

end GS.Topology.SingularHomotopy
