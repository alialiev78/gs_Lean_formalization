# Blockwise geodesics in the orthogonal matrix orbit

For independent orthogonal blocks, the scalar-shuffle condition `k₁ ≥ b₂`
gives an explicit geodesic in the **matrix orbit itself**, through every point
and every tangent vector. The construction only requires exponentials of the
individual block generators.

The metric is the Frobenius metric induced by the inclusion into real matrices.
There is no change to the topology, no sharing constraint, and no
special-unitary statement in this result.

## 1. Dimensions and the exact permutation

Let

\[
n=k_1b_1=k_2b_2,\qquad b_1,b_2>0,\qquad b_2\leq k_1.
\]

Here `b₁` is the size of a right-layer block and `k₁` is the **number** of those
blocks. The analogous left-layer quantities are `b₂` and `k₂`. In zero-based
scalar indices, the permutation used in the project is

\[
\sigma(i)=(i\bmod b_1)k_1+\lfloor i/b_1\rfloor,
\qquad 0\leq i<n.
\]

Write \(P=\operatorname{permMatrix}(\sigma)\). Its convention is
\(Pe_i=e_{\sigma(i)}\). In the output coordinates, the original right-block
label becomes

\[
\left\lfloor\frac{\sigma^{-1}(i)}{b_1}\right\rfloor=i\bmod k_1.
\tag{1}
\]

The formulas are proved for the existing `GS.scalarShuffle`; its numeric action
is not an additional assumption. The cast version `scalarShuffleOfSize` handles
an ambient `Fin n` with an explicit equality `n = k₁*b₁`.

Suppose indices `i,j` belong both to the same left block and to the same
permuted right block. Then

\[
\lfloor i/b_2\rfloor=\lfloor j/b_2\rfloor,
\qquad i\equiv j\pmod{k_1}.
\]

The first equality gives \(|i-j|<b_2\leq k_1\); the second makes `i−j` a multiple
of `k₁`. Therefore `i=j`. This is exactly the no-off-diagonal-overlap condition.

The regular-block theorem records both dimension factorizations. The argument
also allows a final partial left block, so the more general theorem does not
need left divisibility.

## 2. The actual orbit and its tangent vectors

Let \(K_2\) and \(K_1\) be the block-diagonal orthogonal groups for the left and
right partitions. The matrix orbit is

\[
\mathcal M=\{LPR:L\in K_2,\ R\in K_1\}\subseteq\mathbb R^{n\times n}.
\]

It carries its inherited subspace topology and the constructed
horizontal manifold atlas. The induced metric is

\[
g_X(V,W)=\langle V,W\rangle_F=\operatorname{tr}(V^TW).
\]

At \(X=LPR\), every tangent vector is

\[
V=LC PR+LP\Omega R
 =L(C+P\Omega P^T)PR,
\tag{2}
\]

where

\[
C=\operatorname{diag}(C_1,\ldots,C_{k_2}),\quad C_j^T=-C_j,
\qquad
\Omega=\operatorname{diag}(\Omega_1,\ldots,\Omega_{k_1}),\quad
\Omega_r^T=-\Omega_r.
\]

This is a theorem about the inclusion differential from the actual manifold
tangent space. It is not a definition of a replacement tangent space.

In common left coordinates, put

\[
\mathfrak a=\operatorname{Lie}(K_2),\quad
\mathfrak b=P\operatorname{Lie}(K_1)P^T,\quad K=P\Omega P^T.
\]

By Section 1, these skew-matrix spaces have disjoint off-diagonal supports.
Skew matrices have zero diagonal, hence

\[
\mathfrak a\perp_F\mathfrak b,\qquad
\mathfrak a\cap\mathfrak b=\{0\}.
\tag{3}
\]

For a fixed factorization of `X`, equation (2) therefore determines `C` and
`Ω` uniquely. They can be recovered by pulling `V` back to
\(S=L^TVR^TP^T\), masking `S` to the left support to get `C`, and masking it to
the permuted right support to get `K`; then \(\Omega=P^TKP\).

## 3. The explicit blockwise formula

For every real `t`, define

\[
\boxed{\gamma(t)=L\exp(tC)P\exp(t\Omega)R.}
\tag{4}
\]

The exponential is the usual convergent matrix power series. Since a power of
a block-diagonal matrix has the same blocks, termwise summation gives

\[
\exp(tC)=\operatorname{diag}\bigl(\exp(tC_1),\ldots,
\exp(tC_{k_2})\bigr),
\]

and likewise for `Ω`. Thus (4) really is blockwise: no dense `n×n` exponential
is needed.

The exponentials are orthogonal because the generators are skew. Their block
supports are unchanged. Consequently \(\gamma(t)\in\mathcal M\) for all real
`t`, \(\gamma(0)=X\), and

\[
\dot\gamma(0)=V.
\]

Write \(L_t=L\exp(tC)\), \(R_t=\exp(t\Omega)R\), and \(S=C+K\). Direct
differentiation gives

\[
\dot\gamma(t)=L_t S P R_t,
\qquad
\ddot\gamma(t)=L_t\bigl(C^2+2CK+K^2\bigr)PR_t
 =L_t\bigl(S^2+[C,K]\bigr)PR_t.
\tag{5}
\]

Both identities are verified by actual derivative theorems for the exponential
curves. No factor ODE is supplied as a hypothesis.

## 4. Why this is a geodesic for the induced metric

At the current point \(\gamma(t)\), the full tangent space consists of

\[
L_t(D+E)PR_t,\qquad D\in\mathfrak a,\quad E\in\mathfrak b.
\]

The acceleration in (5) is normal to every such vector. Indeed:

1. `S` is skew, so \(S^2\) is symmetric and is Frobenius-orthogonal to every
   skew matrix.
2. For \(D\in\mathfrak a\), invariance of the Frobenius inner product on skew
   matrices gives
   \[
   \langle[C,K],D\rangle_F=\langle K,[D,C]\rangle_F=0,
   \]
   since \([D,C]\in\mathfrak a\) and (3) holds. Likewise, for
   \(E\in\mathfrak b\),
   \[
   \langle[C,K],E\rangle_F=\langle C,[K,E]\rangle_F=0.
   \]
3. Multiplication on the left and right by orthogonal matrices preserves the
   Frobenius inner product.

Therefore

\[
\Pi_{T_{\gamma(t)}\mathcal M}\ddot\gamma(t)=0
\qquad\text{for every }t\in\mathbb R.
\tag{6}
\]

For an embedded manifold with the induced Euclidean metric, the connection

\[
\nabla_U W=\Pi_{T\mathcal M}(DW[U])
\]

is metric-compatible: pairing with tangent vectors removes the discarded
normal components from the ordinary product rule. It is torsion-free because
the difference of the two ambient directional derivatives is the vector-field
bracket, which is tangent. It is consequently the Levi-Civita connection of
the induced metric. Equation (6) is exactly

\[
\nabla_{\dot\gamma}\dot\gamma=0.
\]

This proves the geodesic assertion directly in the matrix orbit. An abstract
quotient or covering-space assertion is not being used in place of (5)–(6).

The speed is

\[
\|\dot\gamma(t)\|_F^2=\|C\|_F^2+\|\Omega\|_F^2
 =\sum_j\|C_j\|_F^2+\sum_r\|\Omega_r\|_F^2.
\tag{7}
\]

The curve exists for all real times. Every initial tangent vector is covered
by (2), so this supplies an explicit complete geodesic construction in this
regime. Geodesic uniqueness, as an ordinary smooth ODE fact, identifies it
with the Riemannian exponential curve. A separately packaged Lean uniqueness
or Riemannian-exponential-map theorem is not claimed here.

## 5. What the new Lean modules prove

`GS/Geodesics/ShuffleCondition.lean` proves the exact permutation action,
inverse block label (1), and no-overlap from `b₂ ≤ k₁`.

`GS/Geodesics/OrbitBlock.lean` defines `blockExpCurve` with target
`MatrixOrbit`, using the existing inherited-topology atlas. Its public results
include:

| Theorem | Verified content |
|---|---|
| `blockExpCurve_contMDiff` | Analytic, hence smooth, curve into the actual orbit |
| `blockExpCurve_hasDerivAt` | Actual matrix first derivative in (5) |
| `blockExpVelocity_hasDerivAt` | Actual matrix second derivative in (5) |
| `blockExpCurve_mfderiv_one` | The explicit velocity is the inclusion image of the actual `mfderiv` of the curve |
| `blockExpVelocity_tangent` | Its tangent lift is exactly that actual curve derivative |
| `blockExpAcceleration_projected_zero` | Equation (6) at every real time |
| `blockExpCurve_covariantVelocity_zero` | The established induced projected operation is zero in the actual tangent fibre |
| `blockExpCurve_constant_speed` | Equation (7) |
| `exists_blockExpCurve_of_tangent` | Every actual initial tangent vector has this construction |

`GS/Geodesics/OrbitShuffle.lean` specializes these results to the actual scalar
shuffle. The theorem `scalarShuffle_blockExpCurve_geodesic` combines both
derivative identities and zero covariant velocity, assuming only positive
block sizes and `b₂ ≤ k₁`. The theorem
`scalarShuffle_exists_blockExpCurve_of_tangent` covers every actual initial
tangent. `regularScalarShuffle_blockExpCurve_geodesic` explicitly records
`n = k₁*b₁ = k₂*b₂`.

The connection operation used here is the existing `covariantAlong`, whose
output is in the actual orbit tangent fibre. The supporting modules establish its
induced metric identities and the symmetry of its coordinate Christoffel
expression. The project does not yet register this operation as a global
mathlib connection object; the new theorem neither assumes such a registration
nor introduces a replacement `IsGeodesic` definition. The ordinary geometric
identification is given in Section 4.

## 6. Scope

The result permits arbitrary orthogonal factors, including components with
negative determinant. It applies to any positive block sizes satisfying the
inequality, including sizes `4`, `8`, and larger. It is not restricted to a
small-dimensional reduction.

The proof uses independent blocks. Sharing imposes additional relations on
the generators and is outside this theorem. With overlap the commutator in
(5) can have a tangent component, so the constant two-factor exponential curve
need not be a geodesic. The three-exponential formula and the distinction
between the induced metric and the standard product quotient metric are
treated in [ORTHOGONAL_GEODESICS.md](ORTHOGONAL_GEODESICS.md).
