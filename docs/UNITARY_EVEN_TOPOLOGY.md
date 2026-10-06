# Even-q topology: a concrete route and its formalization boundary

This note concerns independent unitary three-factor families with p = 2 and
**even q > 2**. The complete ordinary mathematical nonmanifold proof for every
q > 2 is in [UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md). The issue
here is narrower: whether the existing Lean sphere-retraction machinery can
certify the remaining odd cone widths without a new torsion-sensitive
topological argument.

The statements and calculations below are ordinary mathematical reasoning.
This note does **not** assert a Lean theorem for the suspended projective-plane
obstruction or for the even-q topological conclusion.

## 1. The precise cone

The local model is

\[
\mathbb R^e\times C_{3,d},\qquad
C_{3,d}=\{W\in\mathbb R^{3\times d}:\operatorname{rank}W\le1\},
\]

where d = (q - 1)^2 and e = q^2 + 6q - 3. For even q > 2, d is odd and d >= 9.
Every nonzero rank-one matrix has a pivot chart of dimension d + 2. Thus any
Euclidean chart at the vertex of the product would have dimension e + d + 2:
its open source contains a nonzero rank-one point, where the chart dimensions
must agree. The existing Lean theorem
`GS.NonmanifoldTopology.dimensions_of_overlapping_charts` supplies this
comparison once the relevant charts have been constructed.

## 2. A uniform projective-plane retract

Let P be the cone of positive semidefinite, symmetric, rank-at-most-one real
3-by-3 matrices. For d >= 3 define

\[
r(W)=
\begin{cases}
 WW^{\mathsf T}/\|W\|_F,&W\ne0,\\
 0,&W=0,
\end{cases}
\qquad
s(H)=[\,H\mid 0\,].
\]

If W = uz^T with ||u|| = 1, then

\[
WW^{\mathsf T}=\|z\|^2uu^{\mathsf T},\qquad
\|r(W)\|_F=\|W\|_F.
\]

For H in P, positivity and rank at most one imply
H^2 = ||H||_F H. Therefore r(s(H)) = H, including H = 0. Both maps are
continuous; continuity of r at zero follows from its norm identity. Both
preserve the Frobenius norm, and r is homogeneous for nonnegative scalars.

The unit link of P consists of the matrices uu^T with u in S^2. The map
u -> uu^T has exactly the antipodal fibres and induces a homeomorphism from
RP^2 by compactness. Consequently

\[
K_e=\{(x,H)\in\mathbb R^e\times P:
       \|x\|^2+\|H\|_F^2=1\}
\cong\Sigma^e\mathbb{RP}^2.
\]

For e = 0 this means RP^2 itself; for positive e it is the join of RP^2
with S^(e-1). The product maps (x,W) -> (x,r(W)) and
(x,H) -> (x,s(H)) give a strict retraction on the corresponding unit links.

More strongly, K_e retracts from **every** open neighbourhood of (0,0) with
that single point removed. Normalize (x,r(W)) by its nonzero product norm
for the retraction map. For the section, multiply (x,s(H)) by a sufficiently
small positive constant. Such a constant exists uniformly on compact K_e.
Norm preservation makes their composite the identity. The entire singular
stratum is not removed: points (x,0) with x != 0 remain in the domain.

## 3. What the existing approximation argument can do

A direct variant of the proved sphere-approximation argument gives this
ordinary mathematical lemma:

> Let K be a compact subset of a finite-dimensional real vector space E.
> If dim E < dim F, every continuous map K -> S(F) is nullhomotopic.

Extend the map, viewed as F-valued, to E by Tietze extension. Approximate it
uniformly on K by a smooth map, and subtract a sufficiently small point
outside the smooth map's image. Such points exist because dim E < dim F.
Normalize the resulting nowhere-zero map on all of E. Its restriction is
homotopic to the original map, and the extension is nullhomotopic because E
is contractible. These ingredients already appear in
`GS/Topology/SphereApproximation.lean`; the released source does not introduce
a separate compact-source theorem for this route.

Here K_e is a compact subset of R^e times the space of all real 3-by-3
matrices, of ambient dimension e + 9. A hypothetical vertex chart has
dimension n = e + d + 2, and d >= 9 gives e + 9 < n. Transporting the
retraction from Section 2 through a sufficiently small chart ball and its
radial sphere therefore forces the identity of K_e to be nullhomotopic.

The missing certificate is precisely

\[
\operatorname{id}_{\Sigma^e\mathbb{RP}^2}
\quad\text{is not nullhomotopic.}
\]

This statement is true. Its ordinary integral homology proof is

\[
\widetilde H_{e+1}(\Sigma^e\mathbb{RP}^2;\mathbb Z)
\cong\mathbb Z/2.
\]

A more focused formalization could use the reduced cellular complex

\[
0\longrightarrow\mathbb Z
\xrightarrow{\;2\;}\mathbb Z\longrightarrow0,
\]

in degrees e + 2 and e + 1. The arithmetic quotient is elementary. What is
still required is a proved connection of this complex to the actual suspended
projective plane and homotopy invariance of the resulting invariant. Merely
defining this algebraic complex does not provide that connection.

This route avoids computing local homology for every Euclidean sphere or a
full relative-product theorem. It still needs a new torsion-sensitive
certificate. Covering-space and fundamental-group facts alone do not supply
it: a positive suspension of the connected space RP^2 is simply connected.

## 4. Why a lower-dimensional sphere retract cannot replace RP^2

There is a mathematical obstruction to extending the existing sphere-only
method when d is odd. The cone link is

\[
L_{3,d}=(S^2\times S^{d-1})/
        ((u,v)\sim(-u,-v)).
\]

For this free action of a group of order two, rational homology of the quotient
is the invariant part of rational homology of the cover. This follows from
the transfer and averaging over the finite group. When d is odd, both sphere
dimensions are even. The antipodal involution acts by -1 on the degree-two
class and by -1 on the degree-(d-1) class, and hence by +1 on their product.
It follows that

\[
H_j(L_{3,d};\mathbb Q)=
\begin{cases}
\mathbb Q,&j=0\text{ or }j=d+1,\\
0,&\text{otherwise}.
\end{cases}
\]

After e suspensions, the only positive-degree rational homology occurs in
degree e + d + 1. A homotopy retraction induces an injection on homology.
Thus a positive-dimensional sphere which is a homotopy retract of the
punctured product must have exactly dimension e + d + 1. This is already the
sphere dimension of its regular Euclidean charts. A disconnected zero-sphere
cannot be a retract of the connected punctured product either.

Therefore **no lower-dimensional sphere retract exists**, even if nonlinear
constructions are allowed. The currently proved sphere-retraction dimension
theorem cannot yield a contradiction by replacing the quaternion map with a
different sphere-valued retraction. The odd-width obstruction genuinely
requires information that rational sphere dimension does not detect.

## 5. Why padding an odd-q example is not yet a substitute

At a block-diagonal base Q = Q_(q-1) direct-sum 1, one cannot simply declare
the off-block couplings to be free smooth coordinates and infer a full
product neighbourhood from the smaller family.

The natural first-order coupling model already has blocks

\[
X_i=S\,\operatorname{diag}(z_i,w_i)\,T^*,
\qquad S,T\in U(2).
\]

Every X_i^* X_j is normal. Two individually attainable configurations are
X_1 = E_11 with all other blocks zero, and X_2 = E_12 with all other blocks
zero. Their sum would have X_1^* X_2 = E_12, which is not normal because its
two Gram products are E_11 and E_22. Thus these coupling directions are not
a vector space. This invalidates the proposed identification of the natural
coupling coordinates with an independent smooth factor.

A different topological product theorem at a different singular base is not
excluded by this calculation. It would require a proof of the full
neighbourhood statement, including these couplings. A principal-block polar
retraction, an embedded smaller subfamily, or a selected parametrized branch
does not establish that statement.

## Current conclusion

The complete mathematical even-q result follows from the written local model
and local-homology calculation in
[UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md). The alternative
projective-plane route above isolates a smaller formal topological target,
but its suspended-RP^2 noncontractibility certificate is not supplied by the
current Lean library. This note does not count that reduction as a completed
formal nonmanifold theorem.
