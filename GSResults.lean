module

public import GS.Results.Algebra
public import GS.Results.CellRank
public import GS.Results.OriginalCellRank
public import GS.Results.Nonmanifold
public import GS.Results.CosineSine
public import GS.Results.UnitaryCosineSine
public import GS.RiemannianCompletion.Procrustes
public import GS.GlobalGeometry.ExactSharing
public import GS.GlobalGeometry.TangentBundleMetric
public import GS.GlobalGeometry.CayleyDescent
public import GS.GlobalGeometry.OverlapDescent
public import GS.GlobalGeometry.SharedFactorCurves
public import GS.GlobalGeometry.SharedDescent
public import GS.Unitary.Factorization
public import GS.Unitary.TangentMetric
public import GS.Unitary.TracelessProjection
public import GS.Unitary.PhaseKernel
public import GS.Unitary.ProjectionRegularity
public import GS.Unitary.FourFactorCounterexample
public import GS.UnitaryNonmanifold.SmoothCounterexample
public import GS.OverlapGeometry.Gradient
public import GS.OverlapGeometry.SmoothMaps
public import GS.OverlapGeometry.BundleRetraction
public import GS.OverlapGeometry.Descent
public import GS.OverlapGeometry.GeodesicConnection
public import GS.OverlapGeometry.GeodesicEnergy
public import GS.Geodesics.BalancedDynamics
public import GS.Geodesics.OrbitShuffle
public import GS.UnitaryManifold.CayleyAtlas
public import GS.UnitaryManifold.TangentBridge
public import GS.UnitaryManifold.Gradient
public import GS.UnitaryManifold.Retraction
public import GS.UnitaryManifold.BundleRetraction
public import GS.UnitaryManifold.CanonicalDescent
public import GS.SharedGeodesics.PhaseGauge
public import GS.UnitaryManifold.ProjectionSmoothness
public import GS.UnitaryManifold.Dimension
public import GS.UnitaryManifold.Descent
public import GS.UnitaryLocalModel.ChartFibres
public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryTopology.MatrixNonmanifold

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Public results of the GS formalization

Start with `GS.Results.Algebra` for structured orthogonal factorizations,
`GS.Results.CellRank` for the exact block-rank membership criterion, and
`GS.Results` for topological singularities of the original three-factor set.
`GS.Results.OriginalCellRank.inA2_iff_block_rank` states that rank criterion
directly for the original `GS.InA2` class and its actual permutation matrix.
`GS.RiemannianCompletion` contains the actual tangent metric, intrinsic
gradient, and Procrustes objective. `GS.GlobalGeometry` contains the exact
shared-generator projection and normal equations, actual tied factor curves,
smooth tangent-bundle metric evaluation, and Cayley descent results.

The original no-overlap atlas remains available alongside the construction
in `GS.OverlapGeometry` for two independent factors with arbitrary overlap.
The latter retains the inherited matrix topology, identifies the actual
manifold tangent image, and supplies its smooth positive Frobenius metric
and intrinsic gradient of a restricted differentiable loss.
The arbitrary-overlap atlas carries a smooth Cayley retraction on
the whole tangent bundle and intrinsic Armijo/backtracking results.
The geodesic branch proves moving-generator acceleration, the exact overlap
residual, bracket normality, balanced cancellation, symmetric coordinate
Christoffel coefficients, metric compatibility, and constant speed. The
actual matrix-orbit block-exponential geodesic is proved for every initial
tangent under the exact scalar-shuffle inequality k1 >= b2. The arbitrary-
overlap three-exponential integration remains an ordinary mathematical proof
in docs/ORTHOGONAL_GEODESICS.md, separate from a global geodesic-flow interface.
Tied factor curves require positive full block sizes. Read the actual theorem
types and docs/RESULTS.md for their scope.
The broader arbitrary-row rank-one goal remains a separate unproved specification.
`GS.Results.CosineSine` proves the full real square CS decomposition and the
exact scalar GS specialization that exhausts the orthogonal group.
`GS.Unitary` contains complex structured QR/RQ and two/three-factor unitary
sufficiency, real Frobenius projection formulas, and generator metric/kernel
identities. At four factors, `GS.UnitaryFour.counterexample` disproves unitary
sufficiency. `GS.UnitaryNonmanifold` disproves embedded differentiable
smoothness of an explicit three-factor unitary family. These are distinct
obstructions. `GS.UnitaryManifold` constructs the actual two-factor
unitary manifold in its inherited topology, with arbitrary overlap and the
full phase kernel, and identifies its tangent image. The unitary CS branch
proves exact scalar (p,2,p) exhaustion of U(2p).
The unitary manifold also has an actual tangent projector, a smooth positive
Frobenius metric, an intrinsic gradient, and a canonical smooth retraction
on the whole actual tangent bundle. Its point-only matrix formula is
presentation independent. The chosen fixed-fibre retraction has
its intrinsic Armijo decrease and finite geometric backtracking theorems.
The unitary tangent projector is jointly smooth in the point and input.
`GS.UnitaryLocalModel` proves the actual dephased chart, its dimension,
positive-anchor normalization, exact compact quotient, feasibility, and
full-family neighbourhood coverage. `GS.UnitaryTopology.MatrixNonmanifold`
instantiates the local model for the original scalar matrix family and proves
topological nonmanifoldness for every odd q >= 3 at an explicit matrix.
The all-q local-homology proof in docs/UNITARY_LOCAL_STRUCTURE.md remains an
ordinary mathematical proof; the even-q topological conclusion is not yet
Lean-certified.
-/
