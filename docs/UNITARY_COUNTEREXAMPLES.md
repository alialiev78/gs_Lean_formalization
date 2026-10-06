# Unitary counterexamples at three and four factors

The two counterexamples answer different questions. At four factors, unitary
blocks do not suffice to represent every unitary matrix already representable
by unrestricted complex blocks. At three factors, unitary blocks do suffice,
but the resulting matrix family can fail to be a smooth embedded submanifold.

## Four factors: failure of unitary sufficiency

`GS.UnitaryFour.counterexample` uses a matrix of size six, four factors whose
diagonal blocks have size two, and the prescribed perfect shuffle at each of
the three connectors. It proves

\[
Q\in\mathcal A_4(\mathbb C)\cap U(6),\qquad
Q\notin\mathcal A_4^{\mathrm{unitary}}.
\]

`GS.UnitaryFour.strictInclusion` gives the corresponding strict set inclusion.
The matrix is the existing exact real witness, embedded entrywise into complex
matrices. Its nonmembership is proved against arbitrary complex unitary
factors; real nonmembership alone would not imply that conclusion.

Write \(d_{ij}=|\det A_{ij}|\) for the consecutive two-by-two output blocks,
with indices starting at zero. Whenever \(d_{21}d_{10}d_{11}\ne0\), every
matrix in this four-unitary-factor family satisfies

\[
\left(1-\frac{d_{02}d_{10}}{d_{21}}\right)
\left(1-\frac{d_{02}d_{21}}{d_{10}}\right)
\ge \frac{d_{00}d_{22}}{d_{11}}.
\]

The proof establishes this necessary inequality directly for complex unitary
factors. Its ingredients are:

- Left and right multiplication of a block by unitary matrices preserves the
  modulus of its determinant.
- For a two-by-two unitary matrix, opposite entry moduli agree and the squared
  moduli in each row sum to one.
- The middle-factor determinant table therefore has the same nonnegative
  parametrization as in the real certificate.

For the exact witness, the determinant-modulus table is

\[
(d_{ij})=
\begin{pmatrix}
3\sqrt6/16&1/8&3/8\\
3\sqrt6/16&3/8&1/8\\
1/16&3\sqrt6/16&3\sqrt6/16
\end{pmatrix}.
\]

All three denominators are positive. The two sides of the required inequality
reduce to \(25/64\) and \(9/16\), respectively, so the inequality fails.
Extra complex phases cannot change this modulus obstruction.

Main sources: `GS/Unitary/RealEmbedding.lean`, `FourFactor.lean`, and
`FourFactorCounterexample.lean`.

## Three factors: failure of embedded smoothness

The family is the original scalar-indexed complex GS family

\[
\mathcal S=\{M:\operatorname{CInA3Unitary}(2,3,2;P,P^*)\,M\},
\qquad P=P(3,2).
\]

The base point, in consecutive two-by-two block coordinates, is
\(X=Q_0\otimes I_2\), where \(Q_0=I_3-\tfrac23J_3\) and every entry of
\(J_3\) equals one. This is a rational unitary matrix belonging to the family.

For every matrix in this family, the Hermitian Gram matrices
\(M_{ij}M_{ij}^*\) of the blocks within any fixed block row commute. The exact
scalar-shuffle bridge proves this for the original matrix family, without a
supplied local factor lift.

If \(M(0)=X\) and \(M'(0)=V\), define

\[
G_{ij}(V)=V_{ij}X_{ij}^*+X_{ij}V_{ij}^*.
\]

At this base point each block Gram matrix is scalar. Subtracting its scalar
constant term, dividing by the curve parameter, and taking the limit shows
that the matrices \(G_{ij}(V)\) in each row must commute. This argument applies
to every differentiable feasible curve, rather than only to curves with
differentiable chosen factors.

Two explicit feasible rotation curves have velocities \(V_A,V_B\). For their
sum, the first two Gram derivatives in block row zero are

\[
G_{00}(V_A+V_B)=
\begin{pmatrix}-8/25&-32/75\\-32/75&8/25\end{pmatrix},\qquad
G_{01}(V_A+V_B)=
\begin{pmatrix}4/9&0\\0&-4/9\end{pmatrix}.
\]

Their commutator is nonzero, with off-diagonal entries \(256/675\) and
\(-256/675\). Thus the actual feasible curve velocities are not closed under
addition.

A differentiable local ambient retraction fixes every feasible velocity under
its derivative. Linearity of that derivative would make their sum feasible
as well, by applying the retraction to a straight line. Hence no such
retraction exists. An ambient differentiable chart that flattens the set to
\(F\times\{0\}\) would provide a retraction by coordinate projection, so it
cannot exist either.

The public conclusions are
`GS.UnitaryNonmanifold.unitary_three_no_differentiable_local_retraction` and
`GS.UnitaryNonmanifold.unitary_three_no_local_differentiable_flattening`.
The latter excludes every embedded \(C^1\) submanifold chart at the witness,
for arbitrary tangent and normal coordinate spaces. This complex result does
not assert the stronger absence of an abstract topological manifold structure.
The existing real topological nonmanifold theorem remains unchanged.

A separate, complete mathematical proof now establishes the stronger unitary
topological obstruction for every p = 2 and q > 2; see
[UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md). The full
neighbourhood model is now formalized, and
`GS/UnitaryTopology/MatrixNonmanifold.lean` proves topological nonmanifoldness
for every odd q >= 3 in the original scalar-indexed family. The even-q
conclusion and the all-q homology calculation remain ordinary written proofs.
This does not change the narrower scope of the differentiable-obstruction
theorems listed here.

Main sources are in `GS/UnitaryNonmanifold/`: the block invariant, scalar
bridge, derivative obstruction, explicit curves, and final counterexample.
`RetractionObstruction.lean` supplies the general implication from nonadditive
curve velocities to the absence of embedded differentiable charts.
