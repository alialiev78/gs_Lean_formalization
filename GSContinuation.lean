module

public import GS.Continuation.AmbientProjection
public import GS.Continuation.CompactCoverageTools
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialChart
public import GS.Continuation.ExponentialCurves
public import GS.Continuation.FactorCurveVelocities
public import GS.Continuation.PointedCompactImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Exponential coordinates, factor-curve velocities, and compact local models.
See docs/RESULTS.md for the scope of these results. -/
