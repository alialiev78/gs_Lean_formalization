# Actual unitary tangent geometry and optimization interfaces

The two-factor unitary orbit is treated as a real manifold, with the topology
inherited from complex matrices. The first sections describe independent blocks, with arbitrary overlap and
the continuous phase stabilizer. The final section describes the new complete-
block sharing construction and its precise verification boundary.

## An actual point-only tangent projector

For a matrix X in the orbit, define the real linear space

\[
\mathcal T_X=\{CX+X\Omega:\ C^*=-C,\ \Omega^*=-\Omega,
\quad C,\Omega\text{ have the prescribed left and right supports}\}.
\]

`GS/Unitary/PointProjection.lean` constructs its orthogonal projector for

\[
\langle A,B\rangle_{\mathbb R,F}
=\operatorname{Re}\operatorname{tr}(A^*B).
\]

The construction uses a separate real Euclidean encoding of complex matrices.
It retains the existing matrix topology and norm instances. It does not
replace the chart norm by a claimed Frobenius isometry.

The space and its projector depend only on X and the two supports. Their
equality with the supported factor differential is proved for every valid
unitary factor presentation. The module proves range membership, fixed
points, idempotence, self-adjointness, orthogonality of the residual, the
Pythagorean identity, and the unique least-squares property.

`GS/UnitaryManifold/PointProjection.lean` identifies the same space with the
image of the actual manifold inclusion differential, and proves the unique
lift of each projected matrix into the genuine tangent fibre.

`GS/Unitary/SmoothPointProjection.lean` now identifies this point projector
with a polynomial expression in X and the input matrix. The proof uses the
commuting transported masks and the actual Frobenius orthogonality
characterization. `GS/UnitaryManifold/ProjectionSmoothness.lean` proves
`pointProjection_joint_contMDiff` on the actual orbit times the ambient
matrix space. Smoothness of the lifted intrinsic gradient as a tangent-bundle
section remains a distinct interface task.

## Smooth positive metric on the actual tangent bundle

For the inclusion i of the orbit into matrices, the metric is

\[
g_X(v,w)=\langle D i_X(v),D i_X(w)\rangle_{\mathbb R,F}.
\]

`GS/UnitaryManifold/Riemannian.lean` proves bilinearity, symmetry, positive
definiteness and compatibility with the existing finite-dimensional tangent
topology. It also proves smoothness of metric evaluation on the actual
tangent bundle. The positive definiteness uses the proved
injectivity of the genuine inclusion differential.

## Intrinsic gradient

`GS/UnitaryManifold/FrobeniusDual.lean` represents real-linear covectors on
complex matrices using their real and imaginary matrix-unit coefficients.
The resulting ambient gradient represents the actual real Frechet derivative
of a differentiable scalar loss.

`GS/UnitaryManifold/Gradient.lean` projects that ambient gradient and takes
its unique actual tangent lift. The result satisfies

\[
g_X(\operatorname{grad} f,v)=D(f\mathbin{|}_{\mathcal M})_X(v)
\]

for every genuine tangent vector v. The module identifies this derivative
with mathlib's manifold derivative of the restricted loss, proves uniqueness,
and relates stationarity to vanishing intrinsic gradient.

These are intrinsic statements on the constructed unitary manifold. The
projector construction does not yet supply a proved floating-point algorithm,
an asymptotic runtime bound, or global optimizer convergence.

## Retractions and geodesics

A canonical unitary Cayley retraction is proved on the entire actual
tangent bundle, including joint base-point smoothness, feasibility, the zero
section, and the identity fibre derivative. Its matrix formula uses only the
point and its ambient tangent vector; see [RETRACTIONS.md](RETRACTIONS.md).

The fixed-base retraction and its existing descent interface remain
available. `GS/UnitaryManifold/Descent.lean` proves initial negative-gradient
decrease, Armijo decrease for sufficiently small positive steps, and finite
geometric backtracking for that map. `CanonicalDescent.lean` proves the
corresponding results for the canonical map. Convergence of an entire
optimization sequence remains separate.

[ORTHOGONAL_GEODESICS.md](ORTHOGONAL_GEODESICS.md) also proves a mathematical
unitary counterpart of the three-exponential geodesic formula. Its integration
and full intrinsic geodesic interface are not yet Lean-certified. The phase
intersection generally prevents the real no-overlap finite-covering shortcut.

## Complete-block unitary sharing

`GS/UnitarySharing/` supplies the actual orbit atlas and intrinsic
optimization interfaces. The construction
allows arbitrary within-layer repetition of complete physical blocks. The
preceding independent-layer modules remain separate; their simpler mask
formulas are not asserted for arbitrary sharing.

Let `s2,s1` be patterns with positive block sizes dividing n, and let K2,K1
be the actual tied unitary groups. The carrier P is any fixed complex matrix,
including a singular or zero matrix. The orbit is K2 P K1 with its inherited
matrix topology, regarded as a real manifold. No phase directions are removed
from its skew-Hermitian generator spaces.

### Atlas and full tangent image

The checked `Algebra`, `Factors` and `FactorCharts` establish the tied real
star algebra, inverse/Cayley closure, compact factor Lie groups and real charts.
The full factor differential and nonlinear stabilizer agree in Cayley
coordinates. The checked `LocalProduct` and `ProjectedSlice` supply local
horizontal/kernel product coordinates and inverse-function data for projected
horizontal slices. `HorizontalDifferential` identifies their differential range.

The checked `OrbitAtlas` proves openness in the full orbit and
assembles the actual matrix-orbit atlas. `TangentBridge` then identifies the
genuine inclusion differential with the full range of

\[
D_X(A,B)=AX+XB.
\]

The checked `LocalSections` constructs local smooth factor sections and local
lifts of matrix-image curves. These interfaces require no global smooth factor
choice or tangent-surjectivity assumption from the caller.

### Exact projection and physical metric

The real pairing is `Re tr(A* B)`. Generator norms are those of the expanded
physical matrices, equivalently sums of unique-block norms weighted by their
multiplicities. `Projection`, `Riemannian` and `SmoothProjection` supply the
canonical point projector, actual tangent metric and smoothness on a fixed
orbit. There is no claim of smoothness across rank-changing off-orbit points.

With q1,q2 the full tied-space projectors, `NormalEquations` uses the adjoint

\[
D_X^*Z=(q_2(ZX^*),q_1(X^*Z)).
\]

The coupled equations `D_X^* D_X v = D_X^* Z` are equivalent to the entire
Frobenius least-squares problem and to `D_X v = Pi_X Z`. Nonoverlap positions
linked by sharing are included. The kernel may be nontrivial; the canonical
minimum-physical-norm solution is supplied by `MinimumNormLift`.

`PhaseKernel` proves that `(iI,-iI)` is a nonzero shared generator pair in
positive dimension and belongs to `ker D_X` for every X. Thus even without
off-diagonal overlap the raw unitary generator map is not injective. This
regression guards the phase-sensitive horizontal construction.

### Canonical retraction and optimization

For a true tangent vector v at X, put `(A,B)=Lambda_X(d i_X(v))`, the
minimum-physical-norm lift. The retraction is

\[
R_X(v)=c_1(A)Xc_1(B),\qquad c_1(A)=(I+A/2)(I-A/2)^{-1}.
\]

`GeneratorAction` and `SmoothLift` establish equivariance and smoothness of
Lambda on each fixed orbit. `BundleRetraction` supplies the whole actual
tangent-bundle function, zero section and identity actual fibre differential.
`CayleyStep` includes invariance under removing the normal input, and equality
of updates for equal tangent projections.

`GradientSection` supplies smoothness of the true bundled intrinsic gradient,
including `C^(r+1)` loss to `C^r` gradient regularity. `Descent` uses this same
canonical retraction for the loss derivative, Armijo decrease and finite
geometric backtracking. These are mathematical exact maps, not verified
floating-point implementations or convergence-rate results.

All names in this table are in `GS.UnitarySharing`:

| Result | Declaration |
| --- | --- |
| Factor Lie-group atlas | `factorIsManifold`, `factorLieGroup` |
| Local horizontal/kernel product | `sliceProductChart`, `sliceProduct_hasFDerivAt_zero` |
| Projected slice inverse-function data | `exists_projectedSliceData` |
| Horizontal differential range | `horizontalOrbit_fderiv_zero_range` |
| Actual shared-family manifold | `inSharedA2Unitary_admits_manifold` |
| Genuine tangent image | `orbit_tangent_image_iff` |
| Smooth point projector | `pointProjection_contMDiff` |
| Full normal equations | `pointNormalEquation_iff_minimizes` |
| Canonical pointwise lift | `minimumNormLift_unique_minimizer` |
| Smooth lift | `minimumNormLift_contMDiff` |
| Whole-bundle retraction | `cayleyRetraction_contMDiff`, `cayleyRetraction_zero_section`, `cayleyRetraction_fibre_mfderiv_zero` |
| Smooth gradient section | `intrinsicGradientSection_contMDiff_of_order`, `intrinsicGradientSection_smooth` |
| Canonical backtracking | `cayleyRetraction_backtracking_terminates` |
| Phase regression | `pointMap_not_injective` |

General unitary geodesics are outside the formalized scope. A global equivalence
between this shared atlas specialized to distinct labels and the separate
independent-layer atlas is also not claimed implicitly.
