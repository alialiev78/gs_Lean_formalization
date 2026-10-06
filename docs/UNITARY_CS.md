# Complete unitary cosine-sine decomposition

The results in this document are proved in Lean, with no basis-completion
or nondegeneracy hypotheses. The public entry point is
`GS/Results/UnitaryCosineSine.lean`.

## The theorem

For every integer p >= 0 and every unitary matrix Q of size 2p, there are
unitary p-by-p matrices U1, U2, V1, V2 and real numbers
theta_i in [0, pi/2] such that

\[
Q=
\begin{pmatrix}U_1&0\\0&U_2\end{pmatrix}
\begin{pmatrix}C&-S\\S&C\end{pmatrix}
\begin{pmatrix}V_1&0\\0&V_2\end{pmatrix},
\qquad
C=\operatorname{diag}(\cos\theta_i),\quad
S=\operatorname{diag}(\sin\theta_i).
\tag{1}
\]

In this formula the diagonal entries of C and S are real, embedded in the
complex field. Neither the singular values nor the angles are required to
be distinct or nonzero. The theorem asserts existence; it does not assert
a continuous choice of all factors as Q varies.

The public Lean theorem is `GS.Results.UnitaryCosineSine.square`. It uses
the index type `Fin p` on each summand of `Fin p` plus `Fin p`, which makes
the four p-by-p blocks explicit.

## Column completion, including zero columns

Suppose a complex p-by-p matrix T satisfies

\[
T^*T=\operatorname{diag}(d_i^2),\qquad d_i\in\mathbb R.
\]

For every index with d_i nonzero, divide column i of T by d_i. The resulting
columns are orthonormal: the column Gram matrix gives both unit length and
pairwise orthogonality. Extend this prescribed orthonormal family, with its
original index labels, to an orthonormal basis of the full complex vector
space. Let U be the matrix of that basis. For d_i = 0, the squared norm of
column i of T is zero, so that column itself vanishes. Therefore all columns,
including the zero columns, satisfy

\[
T=U\operatorname{diag}(d_i),\qquad U^*U=UU^*=I.
\tag{2}
\]

This is `GS.UnitaryCS.exists_unitary_mul_diagonal`, proved in
`GS/UnitaryCS/ColumnGram.lean` using the orthonormal basis extension theorem.

## Thin CS decomposition

Write the first block column of Q as the vertical stack of A and B. Its
orthonormality gives

\[
A^*A+B^*B=I.
\]

Apply the Hermitian spectral theorem to A* A. There is a unitary V with

\[
(AV)^*(AV)=\operatorname{diag}(\lambda_i),\qquad
(BV)^*(BV)=\operatorname{diag}(1-\lambda_i).
\]

Every diagonal entry of a Gram matrix is nonnegative, so
0 <= lambda_i <= 1. Set c_i = sqrt(lambda_i) and
s_i = sqrt(1 - lambda_i). Applying (2) to the two matrices gives unitary
U1 and U2 with

\[
AV=U_1\operatorname{diag}(c_i),\qquad
BV=U_2\operatorname{diag}(s_i),\qquad
c_i,s_i\geq0,\quad c_i^2+s_i^2=1.
\tag{3}
\]

This is `GS.UnitaryCS.exists_thin_cs` in `GS/UnitaryCS/Thin.lean`.
The construction remains valid when lambda_i is zero or one, because the
column-completion argument does not divide by the zero columns.

## Recovering the complementary columns

Put L = diag(U1,U2), T = diag(V,I), and

\[
K=\begin{pmatrix}C&-S\\S&C\end{pmatrix},
\qquad C=\operatorname{diag}(c_i),\quad S=\operatorname{diag}(s_i).
\]

The identities C squared + S squared = I and CS = SC imply that K is
unitary. By (3), R = L* Q T has first block column [C; S]. Consequently

\[
K^*R=\begin{pmatrix}I&X\\0&W\end{pmatrix}.
\]

This matrix is unitary. The upper-right block of its column Gram matrix is
X, so X = 0. Its lower-right block then shows W* W = I, hence W is unitary.
It follows that

\[
Q=L K\operatorname{diag}(V^*,W).
\tag{4}
\]

This proves `GS.UnitaryCS.exists_square_cs` in
`GS/UnitaryCS/Square.lean`. Finally, choose theta_i = arccos(c_i).
Nonnegativity and c_i squared + s_i squared = 1 give
theta_i in [0, pi/2], cos(theta_i) = c_i, and sin(theta_i) = s_i.
The angle form is `GS.UnitaryCS.exists_square_cs_angles` in
`GS/UnitaryCS/Angles.lean`.

## The exact scalar perfect-shuffle family

Let P be the matrix of `scalarShuffle 2 p`, with the convention
`P i j = 1` precisely when i is the image of j under that permutation.
The original three-factor scalar GS convention is

\[
M=B_3P_2B_2P_1B_1.
\]

Take P1 = P and P2 = P*. The outer matrices in (1) are block diagonal with
two consecutive blocks of size p. Conjugating K by P yields

\[
PKP^*=\operatorname{diag}_{i=0}^{p-1}
\begin{pmatrix}c_i&-s_i\\s_i&c_i\end{pmatrix},
\tag{5}
\]

in the original consecutive scalar order. Thus (4) supplies the factors

\[
B_3=L,\qquad B_2=PKP^*,\qquad
B_1=\operatorname{diag}(V^*,W),
\]

and cancellation of P* P gives exactly M = B3 P* B2 P B1.
The permutation identities and the original `CBlockDiagonal` support
predicates are proved explicitly in `GS/UnitaryCS/Bridge.lean`.

Conversely, a product of these unitary factors and unitary permutation
connectors is unitary. Therefore

\[
\operatorname{CInA3Unitary}(p,2,p;P,P^*;M)
\quad\Longleftrightarrow\quad M\in U(2p).
\tag{6}
\]

The public theorems are
`GS.Results.UnitaryCosineSine.scalar_exhaustion` and
`GS.Results.UnitaryCosineSine.scalar_family_eq_unitary`.

## Distinguishing the two three-factor block patterns

Equation (6) concerns block sizes **(p,2,p)**: the outer layers each have
two large p-by-p blocks; the middle layer has p small two-by-two blocks.
It proves equality with the full unitary group for every p.

The local singularity problem concerns block sizes **(2,q,2)**: the outer
layers each have q small two-by-two blocks; the middle layer has two large
q-by-q blocks. These patterns agree when p = q = 2, but differ in general.
The CS theorem above does not assert that the second pattern exhausts
U(2q) for q > 2. Its local structure is treated separately in
`UNITARY_LOCAL_STRUCTURE.md`.

## Verification

The six new modules, including the public entry point, compile with the
project's Lean 4.19.0 toolchain and pinned mathlib version using
`lake build GS.Results.UnitaryCosineSine`. Their proofs contain no `sorry`
or added axioms. Release-wide verification is recorded separately in the
project verification directory.
