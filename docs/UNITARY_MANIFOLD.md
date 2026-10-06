# Smoothness of the two-factor unitary GS family

The two-factor family with independent unitary blocks is a smooth **real**
manifold, including arbitrary overlap of the two block patterns. Its topology
is the topology inherited from complex matrices. Complex matrices throughout
this construction are real vector spaces; no complex-manifold assertion is
intended.

The public statement is
`GS.UnitaryManifold.inA2Unitary_admits_manifold`. It applies to the original
scalar family

\[
\{M:\operatorname{CInA2Unitary}(b_1,b_2;P;M)\},
\qquad P=\operatorname{cPermMatrix}(\sigma),
\]

for arbitrary dimension, block sizes, and permutation. The underlying orbit
theorem permits arbitrary finite block-label maps. The original division-based
block predicates determine the meaning of incomplete or zero block sizes;
the statement does not add a divisibility or positivity hypothesis.

The sources also construct a genuine smooth real atlas on each supported
unitary block group. The orbit atlas has a smooth inclusion into matrices with
injective manifold differential. `orbit_tangent_image_iff` identifies its
actual tangent image with the defined unitary generator image.
The actual tangent space also carries a positive smooth real Frobenius metric,
a unique intrinsic tangent projector and gradient. The actual projector is
jointly smooth in the point and ambient direction, and a canonical point-only
Cayley retraction is smooth on the whole actual tangent bundle. The complete
skew-Hermitian model has proved real dimension `q²`. The general block-orbit
dimension formula below remains a separate mathematical calculation.

## Why the phase kernel must be included

Let \(K_L,K_R\) denote the supported unitary block groups. Their product acts by

\[
(L,R)\cdot M=LMR^*.
\]

The orbit of P is exactly the two-factor GS family. Both groups are compact,
and the orbit has its inherited matrix topology. The stabilizer is

\[
H_P=\{(L,R)\in K_L\times K_R:LP=PR\}.
\]

In the unitary case, diagonal phases already give a continuous stabilizer.
Thus a proof based on injectivity of all raw factor coordinates would fail
even when the off-diagonal supports do not overlap. The construction removes
the complete kernel of the orbit differential instead.

## The local construction

Use supported skew-Hermitian matrices as real coordinate spaces. For such a
matrix C, both \(I+C\) and \(I-C\) are invertible. For example,

\[
(I+C)^*(I+C)=I+C^*C
\]

is positive definite. The Cayley map

\[
\operatorname{cay}(C)=(I-C)(I+C)^{-1}
\]

is supported, unitary, and smooth. Its derivative at zero is
\(C\mapsto-2C\). Its local inverse gives an actual partial homeomorphism
onto an open subset of the unitary block group.

At the identity of the factor group, the orbit differential is

\[
D(C,\Omega)=-2CP+2P\Omega.
\]

Choose a real linear complement E of \(\ker D\). Finite dimensionality makes
the complement, its projection maps, and a left inverse of \(D|_E\)
continuous. The following two points supply the complete local chart.

1. Every kernel pair integrates to a genuine stabilizer element. Indeed,
   \(CP=P\Omega\) implies
   \(\operatorname{cay}(C)P=P\operatorname{cay}(\Omega)\).
   In factor Cayley coordinates, multiplication of a horizontal lift and a
   kernel lift has derivative \((h,k)\mapsto h+k\). This is a linear
   equivalence from \(E\times\ker D\) onto the full factor model. The inverse
   function theorem therefore gives a local product decomposition.
2. The horizontal orbit map has injective derivative. Compose it with an
   ambient real linear left inverse of \(D|_E\). A second inverse function
   theorem supplies smooth ambient coordinate functions inverse to the
   horizontal parametrization near zero.

The horizontal image is relatively open in the **whole orbit**. To see this,
use the local product decomposition and the open orbit map. Openness of that
map is proved from the compact quotient--orbit homeomorphism and translations
by stabilizer elements. It is not an assumed property of the proposed chart.

Translate the resulting horizontal slice to every orbit point. Its coordinate
maps are restrictions of smooth ambient maps, so all transitions are smooth.
This gives the atlas in the original topology. Differentiating the local
inverse identity proves injectivity of the actual inclusion differential.
Discarding the kernel preserves the entire derivative image, which establishes
the exact tangent-image theorem.

The argument constructs the charts and their open images. It does not merely
invoke an unformalized assertion that every compact group orbit is a manifold.

## Dimension

`GS.UnitaryManifold.finrank_fullModel` proves that the real dimension of the
full skew-Hermitian model on `q × q` matrices is `q²`. Its coordinate
equivalence includes the imaginary diagonal entries and both real coordinates
of each off-diagonal pair. This is the full unitary model.

The following general orbit count is a mathematical calculation, rather than
a separate proved public Lean formula.

Let the left block sizes be \(r_i\), the right block sizes be \(s_j\), and let
\(t_{ij}\) be the size of the intersection of left block i with the right
block j transported by P. Then

\[
\dim_{\mathbb R}\mathcal M
=\sum_i r_i^2+\sum_j s_j^2-\sum_{i,j}t_{ij}^2.
\]

Indeed, the stabilizer is isomorphic to
\(K_L\cap PK_RP^*=\prod_{i,j}U(t_{ij})\). Equivalently, its Lie algebra
consists of skew-Hermitian matrices with the common refined support. A block
of size t contributes t imaginary diagonal coordinates and two real
coordinates for each unordered off-diagonal pair, giving t squared in total.
Subtracting this kernel dimension from the factor dimension yields the formula.
The atlas and tangent-image statements are formalized; this closed
combinatorial dimension formula is not yet a separate public Lean theorem.

## What this adds, and what remains

The smoothness problem at m = 2 is closed for independent unitary blocks,
including all overlap and phase directions. The intrinsic optimization
interface now uses this actual atlas. `PointProjection.lean` proves the unique
tangent lift and its Frobenius least-squares identity. `Riemannian.lean` pulls
back the pairing \(\operatorname{Re}\operatorname{tr}(A^*B)\), proves positivity
with the original chart norm, and proves
smooth metric evaluation and energy on the actual tangent bundle.
`Gradient.lean` identifies the intrinsic gradient with the tangent projection
of the ambient real Frobenius gradient and proves its Riesz identity,
uniqueness, and differentiable stationarity characterization.

`GS/Unitary/PointGenerators.lean` constructs supported balanced generators as
polynomials of the matrix point and ambient direction. On the orbit, the left
and right tangent projectors commute: in factor coordinates they are commuting
support masks. Their inclusion-exclusion formula is therefore the orthogonal
projector to the full tangent image. `SmoothPointProjection.lean` proves
equality with the defined real-Frobenius projector.
`ProjectionSmoothness.lean` then proves joint smoothness of the actual
projector in the orbit point and ambient direction.

`Retraction.lean` uses the global horizontal Cayley parametrization at a fixed
base point. Its map R_X is smooth on the whole tangent fibre, satisfies
R_X(0)=X, and has actual manifold differential dR_X(0)=id. The dependence on
a chosen factor representative is fixed in this fixed-base theorem.
`BundleRetraction.lean` constructs a distinct canonical map from a
point-only Cayley formula. Its value depends only on X and the included
tangent vector. The map is smooth on mathlib's actual entire tangent bundle,
fixes the zero section, and has identity actual fibre differential there;
arbitrary overlap and phase directions are included. `Descent.lean` proves that
a negative-gradient fibre step has initial loss derivative equal to minus
the squared metric norm. Nonzero gradients give sufficiently small Armijo
steps and finite geometric backtracking, with the standard parameter ranges. See
[UNITARY_OPTIMIZATION.md](UNITARY_OPTIMIZATION.md) and
[RETRACTIONS.md](RETRACTIONS.md) for the exact scope.

Remaining interfaces include a smooth varying-base intrinsic gradient section
under suitable loss regularity and optimizer
convergence theorems. Physical sharing requires its own subgroup
and image-identification results. These remaining tasks do not weaken the
proved manifold, metric, gradient, projector, or total-bundle retraction statements.

See [REMAINING_WORK.md](REMAINING_WORK.md) for difficulty estimates and
[UNITARY_CS.md](UNITARY_CS.md) for the distinct three-factor CS result.
For the separate `(2,q,2)` family, the full original-family neighbourhood
model and odd-q topological singularity theorem are proved; their exact
target retains the actual outer unitary groups and the real rank-one cone.
[UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md) distinguishes that
formal result from the ordinary all-q torsion-homology argument.
