# Explicit geodesics for two orthogonal block layers

This document derives geodesics for the metric induced by the ambient
Frobenius inner product. It treats arbitrary overlap between two independent
block layers. The formula involves three matrix exponentials and reduces to
the familiar product of two exponentials when there is no infinitesimal
overlap.

**Verification boundary.** The arbitrary-overlap three-exponential proof
below is an ordinary mathematical proof; Lean establishes its stated
differential and normal-acceleration components. For the requested
no-off-diagonal-overlap case, the full two-exponential trajectory is now
verified in the actual matrix orbit. `GS/Geodesics/OrbitBlock.lean` proves
smoothness, actual manifold velocity, zero induced covariant velocity,
constant Frobenius speed, and realization of every initial tangent vector.
`GS/Geodesics/OrbitShuffle.lean` applies this to the original scalar shuffle
under k1 >= b2, with positive block sizes. See
[BLOCK_GEODESICS.md](BLOCK_GEODESICS.md) for the exact conventions and theorem
names. No quotient metric is substituted for the induced orbit metric.
Global bundled connection and geodesic-flow interfaces remain separate.

## 1. Coordinates and the metric

Fix two orthogonal block subgroups K2 and K1 of O(n), a permutation matrix P,
and the two-factor family

\[
\mathcal M=K_2 P K_1.
\]

Let a and b be their skew-symmetric support algebras in common left
coordinates:

\[
\mathfrak a=\operatorname{Lie}(K_2),\qquad
\mathfrak b=P\operatorname{Lie}(K_1)P^T.
\]

All orthogonality and projections below use

\[
\langle X,Y\rangle_F=\operatorname{tr}(X^TY).
\]

At a fixed point M0 = L P R, with L in K2 and R in K1, the actual tangent
space is

\[
T_{M_0}\mathcal M
=\{L S P R:S\in\mathfrak a+\mathfrak b\}.
\tag{1}
\]

The map S -> L S P R preserves the Frobenius inner product. Thus the metric
on the common-coordinate tangent core is the ordinary Frobenius metric on
the sum of the two support algebras. It is not, in general, the sum of the
squared norms of an arbitrary pair of factor generators.

Put

\[
\mathfrak h=\mathfrak a\cap\mathfrak b,\qquad
\mathfrak a_0=\mathfrak a\cap\mathfrak h^\perp,\qquad
\mathfrak b_0=\mathfrak b\cap\mathfrak h^\perp.
\]

For block-support algebras, the orthogonal projections onto a and b are
entry masks, so they commute. Their product is the projection onto h.
Consequently

\[
\mathfrak a+\mathfrak b
=\mathfrak a_0\mathbin{\perp}\mathfrak b_0\mathbin{\perp}\mathfrak h.
\tag{2}
\]

In particular, a0 is perpendicular to all of b, and b0 is perpendicular to
all of a. Every tangent core has a unique decomposition

\[
S_0=A+B+Z,\qquad
A\in\mathfrak a_0,\ B\in\mathfrak b_0,\ Z\in\mathfrak h.
\tag{3}
\]

If pi_a, pi_b, and pi_h denote the three mask projections, the components
are explicit:

\[
A=(\pi_a-\pi_h)S_0,\quad
B=(\pi_b-\pi_h)S_0,\quad Z=\pi_hS_0,
\qquad
\Pi=\pi_a+\pi_b-\pi_h.
\tag{4}
\]

Here Pi is the projection onto a + b within the skew-symmetric matrices.
For an arbitrary matrix, first take its skew-symmetric part.

## 2. Two bracket identities

For skew-symmetric matrices, the Frobenius inner product is invariant under
orthogonal conjugation. Its infinitesimal form is

\[
\langle[X,Y],T\rangle_F=\langle X,[Y,T]\rangle_F
=-\langle Y,[X,T]\rangle_F.
\tag{5}
\]

The support spaces a, b, and h are Lie subalgebras. Equation (5) and (2)
give

\[
[\mathfrak a_0,\mathfrak b_0]
\perp\mathfrak a+\mathfrak b.
\tag{6}
\]

Indeed, if A is in a0, B is in b0, and T is in a, then [A,T] is in a,
so the second expression in (5) vanishes. For T in b, use the first
expression and [B,T] in b.

We also have

\[
[\mathfrak h,\mathfrak a_0]\subseteq\mathfrak a_0,\qquad
[\mathfrak h,\mathfrak b_0]\subseteq\mathfrak b_0.
\tag{7}
\]

For example, [Z,A] belongs to a. For W in h,
the identity <[Z,A],W> = -<A,[Z,W]> shows that it is perpendicular to h,
because [Z,W] belongs to h. No assertion that h is an ideal of a or b
is needed. Orthogonal conjugation by exp(tZ) therefore preserves a0 and b0.

## 3. The geodesic equation in moving factor coordinates

Let U(t) belong to K2, and let V(t) belong to P K1 P^T. Write a curve as

\[
M(t)=L U(t)V(t)P R,
\qquad
\dot U=UC,\quad\dot V=KV,
\]

where C(t) belongs to a and K(t) belongs to b. Set S = C + K. Direct
differentiation gives

\[
\dot M=L U S V P R,
\]

\[
\ddot M=L U\bigl(\dot S+C^2+2CK+K^2\bigr)V P R
=L U\bigl(\dot S+S^2+[C,K]\bigr)V P R.
\tag{8}
\]

The tangent space at this point is L U (a + b) V P R. Since S squared is
symmetric, it is orthogonal to every skew-symmetric tangent core. Thus

\[
\operatorname{proj}_{T_{M(t)}\mathcal M}\ddot M
=L U\bigl(\dot S+\Pi[C,K]\bigr)V P R.
\tag{9}
\]

For an embedded manifold with its induced Euclidean metric, the covariant
derivative is the tangent projection of the ambient derivative. This
connection preserves the induced metric by the ordinary product rule and
is torsion-free because the ambient derivative is torsion-free. It is
therefore the Levi-Civita connection. Explicitly, for tangent vector fields
E and F, define

\[
\nabla_EF=\operatorname{proj}_{T\mathcal M}(DF[E]).
\]

Normal components pair to zero with tangent fields, so projecting the two
terms of the ambient product rule leaves the metric-compatibility identity
unchanged. Moreover,
\(\nabla_EF-\nabla_FE=\operatorname{proj}_{T\mathcal M}[E,F]=[E,F]\),
since the bracket of tangent fields is tangent. These identities identify
the connection with the induced Levi-Civita connection, independently of
the coordinate calculations. Accordingly, the geodesic equation is exactly

\[
\boxed{\dot S=-\Pi[C,K].}
\tag{10}
\]

This derives the equation for the actual induced metric. It does not infer
geodesicity from an unrelated quotient metric on the factor group.

## 4. Balanced gauge and exact integration

The kernel of the map (C,K) -> C + K consists of (W,-W) with W in h.
The unique lift of minimal ordinary product norm is the balanced lift

\[
C=A+\tfrac12Z,\qquad K=B+\tfrac12Z.
\tag{11}
\]

By (6) and (7),

\[
\Pi[C,K]=\tfrac12[A,Z]+\tfrac12[Z,B].
\tag{12}
\]

The three terms in the decomposition (2) are orthogonal. Consequently
equation (10), in the balanced gauge, is the explicit system

\[
\dot A=\tfrac12[Z,A],\qquad
\dot B=-\tfrac12[Z,B],\qquad
\dot Z=0.
\tag{13}
\]

Its solution for the initial data in (3) is

\[
A(t)=e^{tZ/2}Ae^{-tZ/2},\qquad
B(t)=e^{-tZ/2}Be^{tZ/2},\qquad Z(t)=Z.
\tag{14}
\]

The following factor curves have exactly the logarithmic derivatives (11):

\[
U(t)=e^{t(A+Z)}e^{-tZ/2},\qquad
V(t)=e^{-tZ/2}e^{t(B+Z)}.
\tag{15}
\]

Indeed,

\[
U^{-1}\dot U=e^{tZ/2}Ae^{-tZ/2}+Z/2,
\quad
\dot V V^{-1}=e^{-tZ/2}Be^{tZ/2}+Z/2.
\]

All exponential factors remain in their required block groups: A + Z and
Z lie in a; B + Z and Z lie in b. Hence (15) is feasible for every real t.

**Explicit geodesic theorem.** Given M0 = L P R and the tangent vector
W0 = L (A + B + Z) P R, the induced-Frobenius geodesic with these initial
data is

\[
\boxed{
M(t)=L\,e^{t(A+Z)}e^{-tZ}e^{t(B+Z)}\,P R.
}
\tag{16}
\]

It is defined for every real time, is feasible, starts at M0, has initial
velocity W0, and satisfies (10). More explicitly, substituting (12)--(14)
into (8) leaves the acceleration core

\[
S(t)^2+[A(t),B(t)].
\]

The first term is symmetric and the second is perpendicular to a + b by
(6), proving normal acceleration directly. The usual uniqueness theorem
for the smooth geodesic equation gives the unique solution with the
prescribed initial data.

Independence of the chosen factor presentation can also be checked without
using geodesic uniqueness. If L P R = L' P R', put h = L inverse L'. Then
h belongs to both K2 and P K1 P transpose, and
L' = L h, P R' = h inverse P R. Conjugation by h preserves a, b, their
intersection, and their orthogonal complements. The new tangent components
are therefore h inverse A h, h inverse B h, and h inverse Z h. Every
exponential in (16) transforms by the same conjugation, which cancels against
the two changed boundary factors. This proof also includes disconnected
components of the intersection group.

Its speed is constant, with

\[
\|\dot M(t)\|_F^2
=\|A\|_F^2+\|B\|_F^2+\|Z\|_F^2
=\|W_0\|_F^2.
\tag{17}
\]

This follows directly from (14), orthogonality in (2), and orthogonal
invariance of the Frobenius norm.

## 5. The no-overlap covering interpretation

For real block matrices, no off-diagonal overlap means h = 0, since a
skew-symmetric diagonal matrix is zero. Formula (16) then becomes

\[
M(t)=L e^{tA}e^{tB}P R
=L e^{tA}P e^{tP^TBP}R.
\tag{18}
\]

The differential of the factor map has squared norm

\[
\|C+K\|_F^2=\|C\|_F^2+\|K\|_F^2
\]

because a and b are orthogonal. The stabilizer is discrete, and compactness
makes it finite. The factor map is a local isometry for the product of the
standard Frobenius metrics, or equivalently a Riemannian covering onto its
matrix orbit. Product-group geodesics are exponential curves, so their
images are geodesics. This confirms (18) using the covering viewpoint.

With overlap, the standard product metric has a different quotient norm.
The minimal-norm lift (11) satisfies

\[
\|C\|_F^2+\|K\|_F^2
=\|A\|_F^2+\|B\|_F^2+\tfrac12\|Z\|_F^2,
\]

whereas the induced matrix norm in (17) has coefficient one on the overlap
component. Thus the ordinary product-metric quotient is not a Riemannian
submersion model for the required induced metric when h is nonzero. The
correction in (16) accounts for this difference.

## 6. When two fixed exponentials do suffice

For fixed C in a and K in b, equation (9) gives the precise criterion

\[
L e^{tC}e^{tK}P R\text{ is a geodesic}
\quad\Longleftrightarrow\quad\Pi[C,K]=0.
\tag{19}
\]

The criterion is independent of t in these moving coordinates. It holds in
the no-overlap case and whenever C and K commute. For balanced generators
as in (11), the two summands in (12) lie in the mutually orthogonal spaces
a0 and b0, respectively. Thus the criterion becomes

\[
[A,Z]=0\quad\text{and}\quad[Z,B]=0.
\tag{20}
\]

It also holds when Z = 0, even if the block pattern itself has overlap.
In general it fails; a balanced lift alone does not make a fixed product
of exponentials geodesic.

For a concrete example, use indices 1 through 6 and let

\[
\mathfrak a=\mathfrak{so}(\{1,2,3\})\oplus
\mathfrak{so}(\{4,5,6\}),\qquad
\mathfrak b=\mathfrak{so}(\{1,2\})\oplus
\mathfrak{so}(\{3,4\})\oplus\mathfrak{so}(\{5,6\}).
\]

Write Jij = ei ej^T - ej ei^T. Take A = J23, B = 0, Z = J12. Then
C = J23 + J12/2 and K = J12/2 are the balanced lift, but

\[
\Pi[C,K]=[C,K]=-\tfrac12J_{13}\ne0.
\]

Their fixed product exponentials are therefore not geodesic. Formula (16)
correctly reduces in this example to exp(t(J23 + J12)), since the two final
overlap exponentials cancel.

## 7. A formula depending only on the matrix and its tangent vector

Let X belong to the original family, and let T be an actual tangent vector
at X. Set

\[
S=TX^T,\qquad
\mathfrak b_X=X\operatorname{Lie}(K_1)X^T.
\]

The tangent condition says S belongs to a + b_X. The projections onto a
and b_X commute. To see this, choose any presentation X = L P R. Since
R normalizes its own block algebra, b_X = L b L transpose. Since L
normalizes a, simultaneous conjugation by L takes the commuting pair of
projections for a and b to the projections for a and b_X.

The projection onto b_X can be evaluated without choosing factors:

\[
\pi_{b_X}(Y)=X\,\pi_{\operatorname{Lie}(K_1)}(X^TYX)\,X^T.
\]

Set pi_h = pi_a pi_bX and decompose S using (4), with b_X in place of b.
Then the same geodesic is

\[
\boxed{\gamma(t)=e^{t(A+Z)}e^{-tZ}e^{t(B+Z)}X.}
\tag{21}
\]

This form uses only X, T, and the two fixed support projections. It does
not depend on a continuous or canonical choice of GS factors.

## 8. Unitary corollary

The same proof works for two independent block-unitary layers, with every
transpose replaced by conjugate transpose and with the real inner product

\[
\langle X,Y\rangle_{\mathbb R,F}
=\operatorname{Re}\operatorname{tr}(X^*Y).
\]

The two support algebras now consist of skew-Hermitian matrices and are real
Lie algebras. Their orthogonal projections are still commuting support
masks. The bracket identity (5) remains true. The square of a skew-Hermitian
matrix is Hermitian and is orthogonal, for this real inner product, to every
skew-Hermitian matrix. Consequently all arguments from (2) through (17)
and the factor-independence proof carry over verbatim.

In particular, for the unique real-orthogonal decomposition S0 = A + B + Z,
the induced-real-Frobenius unitary geodesic is

\[
M(t)=L\,e^{t(A+Z)}e^{-tZ}e^{t(B+Z)}\,P R.
\tag{22}
\]

The point-only version (21) uses S = T X conjugate-transpose and
b_X = X Lie(K1) X conjugate-transpose.

There is a substantive difference in the no-off-diagonal-overlap case.
For unitary blocks, imaginary diagonal generators survive in the
intersection h. Thus the factor stabilizer is generally positive-dimensional;
the real finite-covering argument in Section 5 does not transfer under that
hypothesis alone. The correction term in (22) handles these phase directions.
The same balanced criterion (20) describes when it can be replaced by two
fixed exponentials.

This is a mathematical unitary corollary. The unitary atlas, actual tangent
image, and smooth positive Frobenius metric are now formalized in
`GS/UnitaryManifold`. That metric result does not by itself formalize a
connection or geodesic-flow predicate. The unitary moving-generator and
exponential-trajectory bridge remains a separate formalization step.

## 9. Scope

The main calculation uses two independent orthogonal block layers and a
permutation connector; Section 8 gives the unitary analogue. More generally,
it applies to compact matrix subgroups whose
orthogonal Lie-algebra projections commute, since that is the property needed
for (2). It does not automatically apply to arbitrary sharing constraints,
more than two factor layers, or an arbitrary pair of subgroups with
noncommuting Lie-algebra projections.

The formula supplies complete geodesics and their initial-value solution.
It does not by itself compute the cut locus, the injectivity radius, or the
shortest geodesic between two prescribed matrices. Those are separate global
problems.


## Full-block sharing and the nonoverlap inequality

This section concerns independent layers with ties between complete physical
blocks in each layer. The carrier is the exact scalar shuffle, with
N = k_1 b_1 = k_2 b_2 and k_1 >= b_2. Arbitrary permutations do not follow
from this numerical inequality alone. The metric is ambient real Frobenius;
expanded physical generators include the multiplicity of every repeated block.

Use common coordinates at P: a = s_2 and b = P s_1 P*, with their Frobenius
orthogonal projections Q_a and Q_b. For skew-Hermitian initial generators
C in a and D in b, put U = Q_a(D), V = Q_b(C). Nonoverlap makes U and V
diagonal, hence commuting. Projection means projection onto the full tied
space, including all equality constraints, not just an overlap mask.

The corrected curve in common coordinates is

    X(t) = L exp(t(C+U)) exp(-t(U+V)) exp(t(D+V)) P R.

Equivalently, with D=P Omega P* and B=P* V P,

    X(t) = L exp(t(C+U)) exp(-tU) P exp(-tB) exp(t(Omega+B)) R.

The left and right factors remain in their tied unitary groups. The core
velocities are C(t)=exp(tU) C exp(-tU) and
D(t)=exp(-tV) D exp(tV). Their diagonal parts are constant, so
Q_a(D(t))=U and Q_b(C(t))=V. The projected acceleration vanishes because

    C'=[U,C], D'=[D,V],
    Q_a([C,D])=[C,U], Q_b([C,D])=[V,D],
    Q_a(D')=0, Q_b(C')=0.

Here all symbols in the last line are evaluated at t when appropriate.
For tied full-block algebras the projection-commutator identities follow
from the bimodule property of Frobenius orthogonal projection, and the
nonoverlap of off-diagonal supports. They do not require the two diagonal
averaging projections to commute with one another.

The conserved squared Frobenius speed is

    ||C||_F^2 + ||D||_F^2 + 2 Re tr(C* D).

The cross term cannot in general be omitted. In the real orthogonal case
skew-symmetric matrices have zero diagonal, U=V=0, and the curve reduces to
L exp(tC) P exp(tOmega) R.

If K belongs to the common generator space, then K is diagonal. Replacing
(C,D) by (C+K,D-K) replaces (U,V) by (U-K,V+K). All three exponential
arguments are unchanged. `GS.SharedGeodesics.correctedWord_gauge_invariant`
records this exact algebraic cancellation independently of the analytic
proof. This explains why the formula is independent of a chosen initial
factor-generator lift; it does not assert a global choice of factorization.


