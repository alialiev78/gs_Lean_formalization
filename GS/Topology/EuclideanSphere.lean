module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Shared Euclidean sphere type

The definition is moved verbatim from NonmanifoldFinal/SphereCoordinates, with
unchanged namespace and type. It allows homology of ordinary balls and spheres
to be checked without importing the GS normalization/local-model construction.
-/
open scoped BigOperators

namespace GS.NonmanifoldFinal

abbrev UnitSphere (κ : Type*) [Fintype κ] :=
  {x : EuclideanSpace ℝ κ // x ∈ Metric.sphere 0 1}

end GS.NonmanifoldFinal
