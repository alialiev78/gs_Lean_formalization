# Orthogonal geodesics with complete-block sharing

This note proves an explicit geodesic formula in the actual matrix orbit,
with its induced Frobenius metric. It allows arbitrary sharing of complete
physical blocks within each of two independent real orthogonal layers.
The block supports must have no off-diagonal overlap after the connector
permutation. The explicit Lean theorems in `GS/SharedGeodesics/Orthogonal.lean`,
`Shuffle.lean` and `FactorIndependence.lean` have passed compilation and the
transitive axiom audit recorded in [VERIFICATION.md](VERIFICATION.md).

## Setting

Let `K2` and `K1` be the two groups of block-diagonal orthogonal matrices.
Within each group, prescribed blocks of the same size are required to be
equal. The sharing labels in the two layers are independent. These are
closed compact matrix subgroups: equality of complete blocks is preserved
by multiplication and transpose. Their Lie algebras consist precisely of
block-diagonal skew-symmetric matrices satisfying the same equalities.
Indeed, differentiating the equalities gives necessity, and exponentiating
such a generator gives a curve in the group and proves sufficiency.

For a permutation matrix `P`, put

\[
\mathcal M=K_2PK_1,\qquad
\mathfrak a=\operatorname{Lie}(K_2),\qquad
\mathfrak b=P\operatorname{Lie}(K_1)P^T.
\]

Assume that any two different coordinates lie together in at most one of
the left-block partition and the permuted right-block partition. Since
real skew-symmetric matrices have zero diagonal, this implies

\[
\mathfrak a\perp\mathfrak b
\quad\text{for}\quad
\langle U,V\rangle_F=\operatorname{tr}(U^TV).
\tag{1}
\]

Sharing can remove permitted generators but cannot introduce new support
entries, so (1) holds for every choice of the within-layer sharing labels.

The compact group `K2 x K1` acts on matrices by `(L,R): X -> L X R^T`.
Thus its orbit through `P` is a smooth embedded compact submanifold with
the inherited matrix topology. Differentiation gives, at `X=LPR`,

\[
T_X\mathcal M
=\{L(C+D)PR:C\in\mathfrak a,\ D\in\mathfrak b\}.
\tag{2}
\]

This standard compact-group orbit argument supplies the ordinary
mathematical manifold statement. The status of the project's direct Lean
atlas implementation is recorded separately in [VERIFICATION.md](VERIFICATION.md).

## The geodesic theorem

For any `X=LPR` and any `W` in its actual tangent space, there are unique
generators `C` in `a` and `Omega` in `Lie(K1)` such that

\[
W=L(CP+P\Omega)R.
\]

Uniqueness here is for the fixed presentation `X=LPR`; it follows from
the orthogonal direct sum in (1). The induced-Frobenius geodesic with
initial point `X` and velocity `W` is

\[
\boxed{\gamma(t)=L\exp(tC)P\exp(t\Omega)R,\qquad t\in\mathbb R.}
\tag{3}
\]

Every exponential is computed blockwise, and equal physical blocks remain
equal for all time. In particular, (3) is feasible for the sharing constraints.

**Proof.** Set `D=P Omega P^T`, `U(t)=exp(tC)`, `V(t)=exp(tD)`, and
`S=C+D`. Then

\[
\gamma(t)=LU(t)V(t)PR,\qquad
\dot\gamma(t)=LU(t)S V(t)PR,
\]

\[
\ddot\gamma(t)=LU(t)\bigl(S^2+[C,D]\bigr)V(t)PR.
\tag{4}
\]

At this point the tangent space is `LU(t) (a+b) V(t)PR`, by (2).
All boundary factors are orthogonal, so these left and right
translations preserve the Frobenius inner product. The matrix `S^2` is
symmetric and is therefore perpendicular to every skew-symmetric matrix.
For skew-symmetric `A,B,E`, trace cyclicity gives

\[
\langle[A,B],E\rangle_F
=\langle A,[B,E]\rangle_F
=-\langle B,[A,E]\rangle_F.
\tag{5}
\]

If `E` lies in `a`, then `[C,E]` lies in `a`, and the last expression in
(5) vanishes by (1). If `E` lies in `b`, then `[D,E]` lies in `b`, and
the middle expression vanishes. Hence `[C,D]` is perpendicular to
`a+b`. Equation (4) shows that the ambient acceleration is normal to the
actual orbit at every time. For an embedded Euclidean submanifold, its
induced Levi-Civita derivative is the tangent projection of the ambient
derivative. Thus `nabla_(gamma') gamma'=0`. The formula has the required
initial data, so uniqueness of the smooth geodesic initial-value problem
proves the assertion. It is defined for every real time. QED.

The proof does not require commuting generators: their commutator is
normal to the orbit, rather than necessarily zero. Equivalently, these
shared trajectories are geodesics of the corresponding independent-block
orbit that remain entirely in the shared orbit; their acceleration is
therefore normal to the smaller tangent space as well.

## Metric, multiplicities, and factor independence

The speed is constant and is exactly

\[
\|\dot\gamma(t)\|_F^2
=\|C\|_F^2+\|\Omega\|_F^2
=\|W\|_F^2.
\tag{6}
\]

These are norms of the expanded physical matrices. If a distinct left
generator block `C_alpha` is repeated `r_alpha` times, and a distinct
right generator block `Omega_beta` is repeated `s_beta` times, then

\[
\|W\|_F^2
=\sum_\alpha r_\alpha\|C_\alpha\|_F^2
+\sum_\beta s_\beta\|\Omega_\beta\|_F^2.
\tag{7}
\]

Using an unweighted norm of the distinct parameter blocks would generally
give a different metric. Formula (7) is the metric induced by the actual
matrix inclusion.

Let `H=K2 intersection (P K1 P^T)`. Nonoverlap forces every matrix in `H`
to be diagonal; orthogonality then forces its diagonal entries to be signs.
Thus `H` is finite, possibly reduced further by the sharing equalities.
For another presentation `L'PR'=LPR`, write `L'=Lh` and
`PR'=h^{-1}PR` with `h` in `H`. Conjugation by `h` preserves both Lie
algebras. The new generators in common coordinates are
`h^{-1}Ch` and `h^{-1}Dh`; conjugation of the exponentials in (3) cancels
against the changed endpoint factors. Hence the trajectory depends only
on `X` and `W`, including across disconnected factor components.

The factor map with the expanded physical Frobenius product metric is
also a finite Riemannian covering of the orbit. Its derivative is an
isometry by (1), and its fibres are translates of the finite stabilizer
`H`. This gives a second interpretation of (3), while the normal-acceleration
proof above establishes geodesicity directly inside the matrix orbit.

## Exact scalar-shuffle condition

For the project's scalar shuffle, suppose

\[
n=k_1b_1=k_2b_2,\qquad b_1,b_2>0,\qquad k_1\geq b_2.
\]

Here `k1` counts right-layer blocks and `b1` is their size. With zero-based
indices, the shuffle is `sigma(i)=(i mod b1) k1 + floor(i/b1)`.
In output coordinates, the permuted right-block label is `i mod k1`.
Two coordinates in the same left block differ by less than `b2`; if
they also share a permuted right block, their difference is divisible by
`k1`. The displayed inequality forces them to coincide. Therefore the
hypothesis of (1) holds, independently of every sharing label, and (3)
applies for arbitrary admissible dimensions and block sizes.

The independent-block scalar-shuffle implication is represented by
`GS.Geodesics.scalarShuffleOfSize_noOverlap`. The new source now connects it
to the genuine shared atlas and induced tangent connection:

| Declaration in `GS.SharedGeodesics` | Exact assertion |
| --- | --- |
| `orthogonalExpCurve_contMDiff` | Smooth actual shared-orbit trajectory for all real times |
| `orthogonalExpCurve_mfderiv_one` | Explicit velocity equals the actual inclusion image of `mfderiv` |
| `orthogonalExpAcceleration_normal` | Normality against the entire genuine shared tangent image |
| `orthogonalExpCurve_covariantVelocity_zero` | Zero projected covariant velocity in the true tangent fibre |
| `orthogonalExpCurve_constant_speed` | Expanded physical Frobenius generator energy |
| `exists_orthogonalExpCurve_of_tangent` | Every genuine initial tangent vector is realized |
| `orthogonalExpCurve_factor_independent` | Same point and initial matrix velocity imply the same exponential curve for every time |
| `scalarShuffle_shared_geodesic`, `scalarShuffle_shared_exists_geodesic` | Exact scalar shuffle with `left.size <= k1` and the stated ambient dimension |

The source proof of factor independence does not assume geodesic uniqueness.
It establishes conjugation/intertwining for the actual convergent exponential
series and proves the spatial map `(A,B) -> AX+XB` injective using the physical
energy identity. The resulting spatial exponential word depends only on the
matrix point and its true velocity. The induced connection is implemented as
`tangentProjection (deriv V)` with metric compatibility; an abstract global
connection or covering-space registration is not claimed.

All declarations in the table are included in the successful scoped build
and axiom audit. This does not certify unlisted modules or register the written
covering-space interpretation as a general Lean API. No unitary geodesic theorem
is added by this extension.
