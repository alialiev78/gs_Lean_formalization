module

public import GS.Nonmanifold.RankOneGeometry
public import GS.Nonmanifold.CircleRetract
public import GS.Nonmanifold.RadialCone
public import GS.Nonmanifold.RadialHomotopy
public import GS.Nonmanifold.RankOneChart
public import GS.Nonmanifold.SkewCoordinates
public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Nonmanifold.OriginalCompactModel
public import GS.Nonmanifold.NormalizationEstimates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Concrete topology of the local cone model and its factor-coordinate maps.
The final nonmanifold theorem is available through GSNonmanifoldTopology. -/
