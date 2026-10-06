module

public import GS.ManifoldCompletion.FactorCoordinates
public import GS.ManifoldCompletion.OrbitAtlas
public import GS.ManifoldCompletion.BlockLieGroup
public import GS.ManifoldCompletion.OrbitSmooth
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.ManifoldCompletion.TangentBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Nonoverlap orbit atlas and tangent-space bridge. -/
