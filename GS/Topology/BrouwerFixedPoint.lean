module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! A proposition recording the closed-unit-ball formulation of Brouwer's theorem.
An unconditional instance is constructed in `GS.Topology.BrouwerBall`. -/
namespace GS.Topology

class BrouwerFixedPoint (E : Type*) [NormedAddCommGroup E] : Prop where
  brouwer_fixed_point (f : Metric.closedBall (0 : E) 1 → Metric.closedBall 0 1)
    (hf : Continuous f) : ∃ x, f x = x

end GS.Topology
