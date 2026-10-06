module

/-
# Complete source entry point

This target collects all project modules, including unconditional proofs of
`GS.Specifications.NonManifoldGoal`, `RestrictedNonManifoldGoal`, and
`OddConeNonManifoldGoal`. The conditional homology reductions retain their explicit
sphere-profile argument; the final topological proof does not use that argument.

See docs/RESULTS.md for the precise scope and docs/VERIFICATION.md for checks.
-/
public import GS
public import GSExtensions
public import GSContinuation
public import GSLieAction
public import GSCayleyCharts
public import GSRevision
public import GSHomologyFunctor
public import GS.NonmanifoldClosure.PuncturedBall
public import GS.NonmanifoldClosure.LowSphereHomology
public import GSDifferentiableObstruction
public import GSNonmanifoldCoverage
public import GSNonmanifold
public import GSNonmanifoldOpenGerms
public import GSNonmanifoldSphereRetract
public import GSNonmanifoldMembership
public import GSNonmanifoldCompletion
public import GSNonmanifoldBridge
public import GSNonmanifoldHomology
public import GSManifoldCompletion
public import GS.GlobalGeometry.ExactSharing
public import GS.GlobalGeometry.IntrinsicCayley
public import GS.GlobalGeometry.MetricTopology
public import GS.GlobalGeometry.ProjectedDerivative
public import GS.RiemannianCompletion.Procrustes
public import GS.NonmanifoldClosure.ChartRetractions
public import GS.NonmanifoldClosure.RegularConeChart
public import GS.RestrictedNonmanifold.Specification
public import GS.RestrictedNonmanifold.SkewDimension
public import GS.RestrictedNonmanifold.Basepoint
public import GS.RestrictedNonmanifold.Differential
public import GS.RestrictedNonmanifold.ConditionalReduction
public import GSNonmanifoldBallHomology
public import GSNonmanifoldClosure
public import GSNonmanifoldTopology
public import GSResults

public import GS.SharedGeometry.Projection
public import GS.SharedGeometry.Differential
public import GS.UnitaryManifold.CanonicalDescent
public import GS.SharedGeometry.FactorCoordinates
public import GS.SharedGeometry.HorizontalModel
public import GS.SharedGeometry.ProjectedSlice
public import GS.SharedGeometry.LocalProduct
public import GS.SharedGeometry.OrbitAtlas
public import GS.SharedGeometry.HorizontalDifferential
public import GS.SharedGeometry.TangentBridge
public import GS.SharedGeometry.Riemannian
public import GS.SharedGeometry.LocalSections
public import GS.SharedGeometry.SmoothProjection
public import GS.SharedGeometry.Gradient

public import GS.SharedGeometry.MinimumNormLift
public import GS.SharedGeometry.GeneratorAction
public import GS.SharedGeometry.SmoothLift
public import GS.SharedGeometry.CayleyStep
public import GS.SharedGeometry.Retraction
public import GS.SharedGeometry.BundleRetraction
public import GS.SharedGeometry.Descent
public import GS.SharedGeometry.GradientSection

public import GS.SharedGeodesics.PhaseGauge
public import GS.SharedGeometry.Connection
public import GS.SharedGeodesics.Orthogonal
public import GS.SharedGeodesics.FactorIndependence
public import GS.SharedGeodesics.Shuffle
public import GS.UnitarySharing.NormalEquations
public import GS.UnitarySharing.GradientSection
public import GS.UnitarySharing.Descent

public import GS.UnitarySharing.PhaseKernel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
