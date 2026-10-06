module

public import GS.Core
public import GS.Frobenius
public import GS.Projection
public import GS.Sharing
public import GS.Shuffle
public import GS.GeometryAlgebra
public import GS.ThreeFactor
public import GS.Fibres
public import GS.CompactFibres
public import GS.OriginalLocalModel
public import GS.M4Certificate
public import GS.M4Obstruction
public import GS.M4Necessary
public import GS.ElementaryConsequences
public import GS.ComplexAlgebra
public import GS.Specifications

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Core algebra entry point. Use `GSResults` for the public theorem interface or
`GSChecked` for the complete source collection. See docs/RESULTS.md for the
scope of each result and docs/VERIFICATION.md for build instructions.
Importing a proposition whose name ends in `Goal` does not prove it.
-/
