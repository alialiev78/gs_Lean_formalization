# Source map

## Entry points

| Import | Purpose |
| --- | --- |
| `GSResults` | Public result interface and selected geometry results |
| `GSChecked` | Complete maintained proof collection, including alternative routes |
| `GS` | Original matrix families, local model, and proposition specifications |
| `GSNonmanifoldTopology` | Unconditional cone obstruction and original-family theorem |
| `GSManifoldCompletion` | No-overlap smooth atlas and tangent identification under `NoOffDiagonalOverlap` |
| `GS.OverlapGeometry.OrbitAtlas` | Arbitrary-overlap atlas on the original two-factor orthogonal matrix family |
| `GS.OverlapGeometry.Riemannian` | Positive smooth Frobenius metric on the actual overlap tangent bundle |
| `GS.OverlapGeometry.Gradient` | Actual tangent projection, restricted-loss differential, and unique intrinsic gradient with arbitrary overlap |
| `GS.OverlapGeometry.BundleRetraction` | Globally smooth Cayley map on the actual tangent bundle, zero section, identity fibre differential |
| `GS.OverlapGeometry.Descent` | Intrinsic arbitrary-overlap Armijo descent and finite backtracking |
| `GS.OverlapGeometry.GeodesicConnection` | Symmetric local Christoffel coefficients and metric-compatibility identities |
| `GS.SharedGeometry.OrbitAtlas` | complete-block shared orbit atlas |
| `GS.SharedGeometry.TangentBridge` | true shared tangent image and exact projector lift |
| `GS.SharedGeometry.Gradient` | intrinsic shared gradient and smooth matrix realization |
| `GS.SharedGeometry.LocalSections` | local smooth sections and differentiable image-curve lifting |
| `GS.Geodesics.OrbitShuffle` | Actual matrix-orbit block geodesics through every tangent under the exact scalar-shuffle condition `k₁ ≥ b₂` |
| `GS.Unitary.FourFactorCounterexample` | Universal complex four-factor obstruction and exact counterexample |
| `GS.UnitaryNonmanifold.SmoothCounterexample` | Three-factor unitary embedded smoothness counterexample |
| `GS.Results.UnitaryCosineSine` | Complete complex CS decomposition and exact `(p,2,p)` scalar-shuffle exhaustion |
| `GS.UnitaryManifold.OrbitAtlas` | Two-factor unitary atlas with arbitrary overlap on the inherited topology |
| `GS.UnitaryManifold.TangentBridge` | Actual unitary manifold tangent-image identification |
| `GS.UnitaryManifold.Riemannian` | Positive smooth real Frobenius metric on the actual unitary tangent bundle |
| `GS.UnitaryManifold.Gradient` | Intrinsic gradient, its Riesz identity, uniqueness, and stationarity |
| `GS.UnitaryManifold.Retraction` | Smooth fixed-base fibre retraction with identity manifold differential |
| `GS.UnitaryManifold.BundleRetraction` | Canonical point-only retraction smooth on the entire actual tangent bundle |
| `GS.UnitaryManifold.ProjectionSmoothness` | Joint smoothness of the established actual tangent projector |
| `GS.UnitaryManifold.Dimension` | Real dimension `q²` of the complete skew-Hermitian model |
| `GS.UnitaryManifold.Descent` | Intrinsic fixed-base Armijo descent and finite geometric backtracking |
| `GS.UnitaryLocalModel.DephasedNeighborhood` | Actual open dephased-slice chart, with inherited topology and proved coverage |
| `GS.UnitaryTopology.Nonmanifold` | Unconditional three-row cone obstruction for positive widths divisible by four; no matrix-family transfer premise |
| `GS.UnitaryTopology.MatrixNonmanifold` | Full original-family neighbourhood model, odd-q topological nonmanifoldness, and explicit singular matrices |

`import GS` provides the core interface. Read the full type of a theorem
listed in [RESULTS.md](RESULTS.md); a `Goal` definition alone is not its proof.

## Mathematical layers

| Location | Contents |
| --- | --- |
| `GS/Core.lean`, `GS/Frobenius.lean`, `GS/Projection.lean`, `GS/Shuffle.lean` | Matrix factors, block support, explicit Frobenius pairing, permutations |
| `GS/CS/` | Column-Gram completion, thin and square cosine-sine decomposition, angles, exact scalar-shuffle bridge |
| `GS/Unitary/` | Complex support, real Frobenius geometry, skew-Hermitian projection, generator metric and phase kernel, smooth trace-free projection, structured QR/RQ, two- and three-factor unitarization, real scalar extension, four-factor unitary obstruction and counterexample |
| `GS/Extensions/`, `GS/Revision/` | QR/RQ, orthogonalization, four-factor obstruction, unequal blocks, sharing, least squares |
| `GS/LieAction/`, `GS/CayleyCharts/` | Compact block groups, stabilizers, quotient topology, Cayley coordinates |
| `GS/ManifoldCompletion/` | No-overlap atlas and intrinsic interfaces; reusable factor charts and differential formulas |
| `GS/OverlapGeometry/` | Horizontal slices, inherited-topology atlas, actual tangent image, Frobenius metric, intrinsic projection and gradient, total-bundle retraction and descent, moving-generator dynamics and local connection identities |
| `GS/SharedGeometry/` | full-block shared groups, quotient, horizontal atlas, actual tangent geometry, local factor sections, smooth projector/lift, canonical whole-bundle retraction, intrinsic descent and smooth gradient section |
| `GS/Geodesics/` | Exact scalar-shuffle condition, actual orbit block-exponential curves and their covariant equation, every initial tangent, bracket support, and balanced residual identities; all-overlap integration remains separate |
| `GS/UnitaryCS/` | Complex column completion, Hermitian thin CS, full square CS, angles, and the exact scalar perfect-shuffle bridge |
| `GS/UnitaryManifold/` | Supported unitary groups and dimension, real Cayley coordinates, compact orbit topology, horizontal and stabilizer slices, actual atlas and tangent image, intrinsic metric and gradient, jointly smooth projector, canonical total-bundle retraction, and fixed-fibre descent |
| `GS/UnitaryLocalModel/` | Pauli coordinates, exact full fibres, normalization, positive polar uniqueness, actual dephased charts and dimension, compact full-image homeomorphisms, feasibility, and coverage of every nearby original-family matrix |
| `GS/UnitaryTopology/` | Quaternion/Clifford sphere retract, regular cone charts, three-row cone obstruction at positive widths divisible by four, full matrix-family neighbourhood model, and odd-q topological nonmanifoldness with explicit points |
| `GS/UnitaryNonmanifold/` | Row-block Gram invariants, exact scalar-shuffle bridge, restrictions on arbitrary curve velocities, explicit curves, embedded smoothness obstruction |
| `GS/RiemannianCompletion/`, `GS/GlobalGeometry/` | Tangent metric, intrinsic gradient, arbitrary-overlap descent, shared normal equations and factor curves, exponential and Cayley steps |
| `GS/OriginalLocalModel.lean`, `GS/Continuation/` | Original parametrizations, equal fibres, exponential coordinates |
| `GS/NonmanifoldCompletion/` | Membership, normalization gauges, full-family local coverage, pointed neighbourhood model |
| `GS/Nonmanifold/`, `GS/NonmanifoldObstruction/`, `GS/NonmanifoldFinal/` | Rank-one coordinates, sphere retractions, transport of local obstructions |
| `GS/Topology/`, `GS/NonmanifoldClosure/` | Brouwer, sphere topology, dimension obstruction, unconditional conclusion |
| `GS/Results/` | Public algebraic contracts, exact cell-rank criterion, determinant-free nonmanifoldness, explicit singular points |

The conditional homology route in `SphereProfile.lean` and
`ConditionalClosure.lean` retains an explicit `SphereHomologyProfile`
parameter. The final theorem in `TopologicalClosure.lean` does not use it.

## Construction principles

Two-factor geometry uses compact supported factor groups, the derivative
kernel and a complementary horizontal space. Local product charts establish
openness in the full matrix orbit; horizontal slices supply its atlas in the
inherited topology. Tangent-image theorems identify actual manifold tangents
with supported generator directions.

Local factor sections and equivariance yield smooth projectors and canonical
minimum-norm lifts. Whole-bundle retractions and genuine tangent maps then
give intrinsic gradients as smooth bundle sections. The unitary construction
uses real Frobenius geometry and retains continuous phase stabilizers.

No-overlap orthogonal geodesics are proved in the actual orbit through every
initial tangent. General overlap integration and global connection interfaces
are separate from the available differential identities.

Many definitions are `noncomputable`: this is a mathematical library, not an
executable numerical optimizer. Explicit `frobInner` and `frobSq` expressions
must not be identified with an unrelated default matrix norm. Hypotheses such
as nonoverlap, differentiability and valid sharing patterns are part of the
theorem types.

The SU draft is located in `experimental/special_unitary/`; it is outside the
supported build. See [RESULTS.md](RESULTS.md), [REMAINING_WORK.md](REMAINING_WORK.md)
and [THIRD_PARTY.md](THIRD_PARTY.md) for the result interfaces, boundaries and
attribution.
