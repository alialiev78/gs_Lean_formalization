module

public import GS.NonmanifoldFinal.HomologyApplication

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Actual induced homology maps for the constructed retract. No sphere homology
computation and no unconditional NonManifoldGoal are asserted. -/
