# Retractions: definitions, verified scope, and remaining work

Two different meanings of retraction occur in this project. They must not be
confused when comparing the smooth two-factor family with the singular
three-factor examples.

## Optimization retractions

For a smooth manifold M, an optimization retraction is a smooth map from a
neighbourhood of the zero section of TM to M such that

\[
R_X(0)=X,\qquad D R_X(0)=\operatorname{id}_{T_XM}.
\]

The second condition is the derivative of the restriction to the fibre over X.
A construction defined on all of TM is stronger than the usual local-domain
requirement. Smoothness on every separate fibre does not, on its own, imply
smoothness as X varies.

The proofs use mathlib's actual `TangentSpace`, `TangentBundle`, `ContMDiff`,
and `mfderiv`. They do not require a preexisting optimization-retraction class:
the map and every defining property are explicit theorems. There is no assumed
retraction oracle.

## The orthogonal construction with arbitrary overlap

`GS/GlobalGeometry/CayleyRetraction.lean` constructs an
ambient update depending only on the matrix X and direction V. Supported
skew-symmetric generators C(X,V) and Omega(X,V) are obtained by a balanced split
of the two commuting tangent projectors. Their reconstruction is

\[
C(X,V)X+X\Omega(X,V)=\Pi_X V.
\]

In particular, it equals V for every actual tangent vector. With

\[
\operatorname{cay}_1(A)=(I+A/2)(I-A/2)^{-1},
\]

the update is

\[
R_X(tV)=\operatorname{cay}_1(tC(X,V))\,X\,
        \operatorname{cay}_1(t\Omega(X,V)).
\]

The denominators are invertible for every real t because the generators are
skew-symmetric. The update preserves the original two-factor support and
orthogonality constraints for all tangent vectors and all real times.
Its ambient extension is jointly smooth in X, V, and t.

The new `GS/OverlapGeometry/Retraction.lean` identifies these properties with
the actual tangent fibres of the arbitrary-overlap atlas. In particular,
`cayleyFibreRetraction_mfderiv_zero` proves the identity differential, and
`cayleyTangentStep_mfderiv_one` proves the prescribed actual manifold velocity.

`GS/OverlapGeometry/BundleRetraction.lean` closes dependence on the base point:
`cayleyRetraction` has domain the whole actual tangent bundle, and
`cayleyRetraction_contMDiff` proves its smoothness. The proof composes the
smooth base-point inclusion and the smooth tangent realization with the
already established ambient Cayley formula. The generic manifold-source
criterion in `ManifoldSmoothMaps.lean` converts this ambient smoothness into
smoothness of the map into the original orbit. No smooth choice of factor
representatives is assumed.

The resulting zero-section and fibre-derivative theorems are
`cayleyRetraction_zero_section` and
`cayleyRetraction_fibre_mfderiv_zero`.

`GS/OverlapGeometry/Descent.lean` also connects this retraction to the actual
Frobenius gradient. For a loss differentiable at X, the initial loss derivative
in the negative-gradient direction is minus the squared metric norm. The
module proves Armijo decrease for sufficiently small positive steps and
termination of geometric backtracking. It does not prove convergence of an
entire optimization sequence or floating-point stability.

## Physical sharing: canonical retraction and intrinsic descent

Orthogonal sharing has true tangent-bundle interfaces, a smooth gradient
section and intrinsic descent. The construction covers complete repeated blocks
within each layer, arbitrary overlap and any fixed real carrier P.

Write S_2 and S_1 for the actual tied skew-generator spaces and set

\[
D_X(A,B)=AX+XB.
\]

`MinimumNormLift.lean` constructs the unique pair Lambda_X(Z) satisfying

\[
D_X\Lambda_X(Z)=\Pi_X Z,\qquad
\Lambda_X(Z)\perp\ker D_X.
\]

Orthogonality here uses \(\|A\|_F^2+\|B\|_F^2\) on the full expanded physical
matrices. In unique-block coordinates it is the multiplicity-weighted sum,
not an unweighted norm. A genuine L2 encoding supplies the kernel projection;
no inner product is installed on the default matrix supremum norm.

The construction is linear in Z at fixed X. Conjugation equivariance and local
smooth sections prove joint smoothness on the fixed matrix orbit. Smoothness
across rank-changing ambient points or across different carriers is not claimed.

For an actual tangent vector v, let V be its matrix realization and
(A,B)=Lambda_X(V). The canonical value is

\[
R_X(tv)=\operatorname{cay}_1(tA)\,X\,\operatorname{cay}_1(tB).
\]

It is defined for every real t, preserves the exact shared orbit, depends only
on X and v, and has initial matrix velocity V. `Retraction.lean` identifies
this with the actual manifold derivative; `BundleRetraction.lean` supplies
joint smoothness on the entire tangent bundle, the zero-section identity and
the identity fibre differential.

`Descent.lean` uses this same function for the intrinsic negative-gradient loss
derivative, strict Armijo decrease and finite geometric backtracking. Only
pointwise differentiability is required there; the gradient must be nonzero.
These are not convergence or computational cost bounds.

`GradientSection.lean` is included in the successful compilation and axiom
audit. It proves smoothness of the actual tangent projector and gradient
section using the derivative of a smooth ambient-input extension of R.
An ambient C^(r+1) loss yields a C^r section, with a C-infinity corollary and
joint regularity of the exact update in point and step size. In the pinned mathlib, the order `∞` means
C-infinity whereas `⊤` (also written `ω`) is analytic order; the C-infinity
corollaries do not assume analyticity.

## The unitary construction

There are two constructions, with different guarantees.
`GS/UnitaryManifold/Retraction.lean` supplies the `fibreRetraction`
using a chosen horizontal chart at each point. Its fixed-fibre smoothness and
identity differential are proved. These facts alone do not prove that this
particular choice varies smoothly with the base point or is independent of
a different factor presentation.

The new `GS/UnitaryManifold/BundleRetraction.lean` instead defines a canonical
map `cayleyRetraction` on the whole actual tangent bundle. For an actual
vector v at X, first take its ambient realization V = Di_X(v). The supported
skew-Hermitian generators C(X,V) and Omega(X,V) are polynomial expressions
in X and V using the two support masks. Their balanced construction is in
`GS/Unitary/PointGenerators.lean`; it reconstructs every actual tangent
matrix:

\[
C(X,V)X+X\Omega(X,V)=V.
\]

The update is the same normalized Cayley formula as in the real case, with
conjugate transpose replacing transpose. `UnitCayley.lean` proves denominator
invertibility, unitarity, smoothness, support preservation, and the derivative
of the normalized transform. `PointCayley.lean` proves all-time feasibility
in the original matrix orbit and the ambient tangent derivative.

This proves that the retraction is a well-defined function, not merely an
existence statement about updates: its matrix value uses only X and V.
A proof of membership in the orbit does not change the subtype value. No
chosen factorization occurs in this value, and no smooth choice of factor
representatives is assumed. Every real step and every actual tangent vector
are allowed, including arbitrary overlap and the phase stabilizer.

The final theorems are `cayleyRetraction_contMDiff`,
`cayleyRetraction_zero_section`, and
`cayleyRetraction_fibre_mfderiv_zero`. They establish joint smoothness on
mathlib's actual tangent bundle, R_X(0) = X, and D R_X(0) = id. The
`canonicalCayleyStep_mfderiv_one` theorem also identifies the actual manifold
velocity. This canonical construction is separate from the chosen
horizontal-fibre map; no equality between those two maps is asserted.

`GS/UnitaryManifold/Descent.lean` proves the intrinsic loss derivative, Armijo
decrease and finite geometric backtracking for the chosen fixed-base map.
`GS/UnitaryManifold/CanonicalDescent.lean` proves the corresponding results
for the canonical whole-bundle map.

## Complete-block unitary sharing

`GS.UnitarySharing.BundleRetraction` proves a canonical
retraction on the entire true tangent bundle of the shared complex matrix
orbit. The construction is real-geometric, uses the full physical Frobenius
minimum-norm lift, and retains the phase kernel. It allows arbitrary fixed
complex carriers and overlap. Its exact value is `c1(A) X c1(B)` with the
same normalized Cayley convention as above; membership in the orbit does not
change that value. `CayleyStep` includes both normal-input invariance lemmas.

The complete unitary sharing construction includes factor
Lie-group charts, inherited-topology orbit atlas, actual tangent bridge,
physical metric, smooth point projection and minimum-norm lift, whole-bundle
zero-section and identity-differential properties, smooth gradient section
and canonical intrinsic descent, with the phase kernel and complete normal
equations retained. See the final
section of [UNITARY_OPTIMIZATION.md](UNITARY_OPTIMIZATION.md) for exact names,
regularity and scope. Cross-layer sharing, partial blocks, polar approximations
and floating-point implementations are not covered by these theorems.

## Ambient neighbourhood retractions

A local ambient retraction is a map from an open ambient neighbourhood into
the matrix subset which restricts to the identity on that subset. This is a
different domain and a different requirement from an optimization retraction
whose domain is a tangent bundle.

The three-factor unitary obstruction in
`GS/UnitaryNonmanifold/RetractionObstruction.lean` excludes a differentiable
local ambient retraction at its singular point. It does not contradict the
two-factor tangent-fibre constructions above.

Likewise, failure of an embedded differentiable chart alone does not exclude
an abstract topological manifold. The stronger topological conclusion for
the unitary `(2,q,2)` family, q > 2, follows from the complete written
neighbourhood and local-homology proof in
[UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md). The actual
full-family neighbourhood model is now formalized for both parities, and
a separate quaternion argument proves topological nonmanifoldness in Lean
for every odd q >= 3. The even-q homology obstruction remains unformalized.


## Special-unitary blocks: the actual whole-bundle exponential retraction

The ordinary normalized Cayley map fails the per-block determinant condition
already in dimension three. The regression theorem records this obstruction. For
an actual SU tangent vector v, set (A,B)=Lambda_X(d iota_X(v)) and define

\[
R_X(v)=\exp(A)X\exp(B).
\]

The experimental source defines a separate SU atlas and tangent bridge, so
`GS.SpecialUnitarySharing.expRetraction` has the whole actual SU tangent bundle
as its domain. Written proofs establish joint smoothness, zero-section
preservation, and identity actual fibre differential. They use the canonical
minimum-physical-norm lift and the existing normal-input invariance lemmas.
The smooth intrinsic gradient section and intrinsic Armijo/backtracking use
this same map. It is not asserted to be the Riemannian exponential map.

The smooth extensions on the surrounding U orbit are distinct.
`IntrinsicSmooth` restricts them through the smooth inclusion of
the independently charted SU orbit. Kernel checking is still outstanding for
the special-unitary sharing proof chain. See
[SPECIAL_UNITARY_SHARING.md](SPECIAL_UNITARY_SHARING.md).
