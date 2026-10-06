# Nonmanifoldness: proof outline

For the original GS family with `p = 2` and `q ≥ 3`, the point `basePoint Q₀`
has no open Euclidean chart when `Q₀` is orthogonal and every entry is nonzero.
The public theorem `GS.Results.gs_not_euclidean_at` removes the determinant-one
restriction of the original specification. All topologies are inherited from
the original matrix spaces. This excludes a manifold without boundary at the
specified point; a manifold-with-boundary assertion is not part of this result.

`GS.NonmanifoldTopology.nonManifold` proves the original specification.
Neither cone nonmanifoldness nor a sphere homology profile is an unproved input.
For every `q ≥ 3`, `GS.Results.reflectionBase_nonEuclidean` uses the explicit
reflection `Q₀ = I − (2/q)J`, with `J` the all-ones matrix. Its orthogonality,
nonzero entries, membership, and nonmanifold conclusion are proved. A separate
orientation adjustment supplies a determinant-one example in every such size.

## From the matrix family to a cone

The original maps `originalF` and `originalG` have the same fibres on a uniformly
small compact parameter domain. Full-family coverage proves that this image
contains a neighbourhood in the original GS family. It therefore controls the
whole local family, rather than a selected parametrized branch.

The pointed neighbourhood model transfers the question to the vertex of

\[
X=\mathbb R^e\times
\{Z\in\mathbb R^{2\times d}:\operatorname{rank}Z\le1\}.
\]

For the original family, `d = q(q−1)/2`, so `q ≥ 3` implies `d ≥ 3`.
The separate two-row cone theorem already holds for every `d ≥ 2`.

## Topological argument

1. **Brouwer fixed point theorem.** The ported combinatorial and analytic proof
   on a simplex retains its authorship and license. An embedding into a simplex
   and a radial retraction yield the theorem on a closed ball in a
   finite-dimensional real space.
2. **Spheres are not contractible.** A sphere contraction would give a retraction
   from a ball onto its boundary. Composing with the antipodal map contradicts
   Brouwer's theorem.
3. **Maps from a smaller sphere to a larger sphere are null-homotopic.** Tietze
   extension, smooth approximation, a point outside the image of a smooth map
   of smaller dimension, and normalization produce the required homotopy.
4. **Punctured-ball retractions determine dimension.** A sphere retract of a
   punctured ball induces maps between spheres whose composite is homotopic to
   the identity. Unequal dimensions would make one map null-homotopic,
   contradicting sphere noncontractibility.
5. **The cone would force two different chart dimensions.** Every punctured
   open neighbourhood of the vertex of `X` retracts onto `S^(e+1)`, forcing a
   putative vertex chart to have dimension `e+2`. The same neighbourhood contains
   a regular point with an explicit chart of dimension `e+d+1`. The dimensions
   of overlapping Euclidean charts must agree, which is impossible for `d ≥ 2`.

This route does not require computing the homology of every sphere. The retained
alternative route with an explicit `SphereHomologyProfile` parameter is separate.

## Main source files

| Step | Source |
| --- | --- |
| Equal fibres and full local coverage | `GS/Continuation/ExponentialChart.lean`, `GS/NonmanifoldCompletion/FullFibreCoverage.lean` |
| Pointed neighbourhood model | `GS/NonmanifoldCompletion/NeighbourhoodModel.lean` |
| Brouwer theorem | `GS/Topology/Brouwer/`, `GS/Topology/BrouwerBall.lean` |
| Sphere noncontractibility | `GS/Topology/SphereNoncontractible.lean` |
| Homotopies between spheres | `GS/Topology/SphereApproximation.lean` |
| Punctured-ball dimension | `GS/Topology/PuncturedSphereObstruction.lean` |
| Cone retractions and regular chart | `GS/NonmanifoldClosure/ChartRetractions.lean`, `GS/NonmanifoldClosure/RegularConeChart.lean` |
| Original specification | `GS/NonmanifoldClosure/TopologicalClosure.lean` |
| Stronger statement and explicit examples | `GS/Results/Nonmanifold.lean` |

See [RESULTS.md](RESULTS.md) for exact theorem names and
[VERIFICATION.md](VERIFICATION.md) for reproducible compiler and axiom checks.
