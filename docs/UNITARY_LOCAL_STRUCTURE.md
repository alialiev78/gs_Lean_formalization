# The local structure of the unitary three-factor family for p = 2

**Verification boundary.** The actual full-family neighbourhood theorem is
now formalized in `GS/UnitaryTopology/MatrixNonmanifold.lean` as
`unitary_matrix_pointed_neighbourhood_model`. Its exact target is
`OuterFactors q o` times `ConeCoordinates ((q-1)^2)`, where the first factor
is U(2)^(2q-1) and `ConeCoordinates d` is R^d times the real three-row
rank-one cone. The inherited matrix topology, actual dephased chart, compact
quotient, feasibility, and coverage of every nearby family member are all
proved. The theorem assumes only a unitary Q with nonzero anchor row and
column, and applies without a parity restriction. The displayed numerical
Euclidean dimension below is an ordinary dimension calculation; the formal
local-model type retains the outer unitary factors.

`unitary_gs_not_euclidean_at` proves the genuine topological obstruction for
**every odd q >= 3**. `unitaryReflection_nonEuclidean` supplies an explicit
singular matrix in the original scalar-indexed family, with no assumed chart
or local-model premise. The proof uses a quaternion contraction and certified
sphere-dimension obstruction, not an assumed local homology computation.
Section 9 describes that formal proof.

The ordinary local-homology argument in Section 7 proves the conclusion for
**all q > 2**, including even q. That homology calculation and the even-q
topological conclusion remain unformalized. See
[UNITARY_EVEN_TOPOLOGY.md](UNITARY_EVEN_TOPOLOGY.md) for the exact outstanding
invariant and why the sphere-only method cannot be extended to those widths.
The embedded-smoothness obstruction in
`GS/UnitaryNonmanifold/SmoothCounterexample.lean` remains a separate theorem.

## 1. The family and the statement

Fix an integer q >= 2. Display a matrix of size 2q as a q-by-q array of
two-by-two complex blocks. Define

\[
\mathcal F_q=
\left\{M:\ M_{ij}=U_i
\begin{pmatrix}A_{ij}&0\\0&B_{ij}\end{pmatrix}V_j,
\quad A,B\in U(q),\quad U_i,V_j\in U(2)\right\}.
\]

This is exactly the original scalar perfect-shuffle family with three block
sizes 2, q, 2, after the fixed coordinate identification proved in
`ScalarBridge.lean`. Throughout, this family has the topology inherited from
the ambient complex matrix space, viewed as a real vector space.

Let Q belong to U(q), and suppose that

\[
Q_{i0}\ne0\quad(0\le i<q),\qquad
Q_{0j}\ne0\quad(1\le j<q).
\]

No nonvanishing assumption is needed on the remaining entries. Set

\[
X=Q\otimes I_2,\qquad d=(q-1)^2,\qquad
s=8q-4+d=q^2+6q-3,
\]

and define the **real** determinantal cone

\[
\mathcal C_{3,d}
=\{W\in\mathbb R^{3\times d}:\operatorname{rank}W\le1\}.
\]

**Theorem.** There are open neighbourhoods of X in the full family
\(\mathcal F_q\) and of \((0,0)\) in
\(\mathbb R^s\times\mathcal C_{3,d}\), and a homeomorphism between them
taking X to \((0,0)\).

The singular factor is a real three-row rank-one cone. It is not a complex
rank-one cone, and its number of columns is not q squared. The row and column
phase freedoms account for the difference.

For every q > 2, an explicit admissible base point is obtained from

\[
D=\operatorname{diag}(1,-1,\ldots,-1),\qquad
Q=D\left(I_q-\frac2q\mathbf1\mathbf1^T\right)D.
\]

Indeed, Q is real orthogonal, its first row and column are positive, its
diagonal entries are \((q-2)/q\), and all its off-diagonal entries have
absolute value \(2/q\).

## 2. A canonical polar normalization

For an invertible complex matrix T, write

\[
\operatorname{pol}(T)=T(T^*T)^{-1/2}.
\]

This is the unitary polar factor. It depends smoothly on T, and for unitary
L and R it satisfies

\[
\operatorname{pol}(LTR)=L\operatorname{pol}(T)R.
\]

In the two-by-two case used here, smoothness needs no choice of eigenvectors.
For a positive definite Hermitian matrix H, the positive square root is

\[
H^{1/2}=\frac{H+\sqrt{\det H}\,I_2}
{\sqrt{\operatorname{tr}H+2\sqrt{\det H}}}.
\]

The determinant and trace are real and positive. Cayley--Hamilton verifies
the square, and the numerator is positive definite. The formula and matrix
inversion are smooth on this open domain and commute with unitary
conjugation. Applied to \(H=T^*T\), they prove both the asserted smoothness
and polar covariance.

For M sufficiently close to X, all anchor blocks \(M_{i0}\) and
\(M_{0j}\) are invertible. Define

\[
W_{i0}=\operatorname{pol}(M_{i0}/Q_{i0}),\qquad
W_{0j}=\operatorname{pol}(M_{0j}/Q_{0j}),
\]

\[
L_i=W_{i0},\qquad
R_j=L_0^*W_{0j},\qquad
N_{ij}=L_i^*M_{ij}R_j^*.
\tag{1}
\]

Here \(R_0=I_2\), exactly. At X all the L and R factors equal the identity.
The first-column and first-row block ratios of N are positive definite:

\[
N_{i0}/Q_{i0}>0,\qquad N_{0j}/Q_{0j}>0.
\tag{2}
\]

Conversely, if N satisfies (2), \(L_i,R_j\in U(2)\), and \(R_0=I_2\),
then the reconstruction

\[
M_{ij}=L_iN_{ij}R_j
\tag{3}
\]

has precisely the factors L and R recovered by (1). For example,
\(M_{i0}/Q_{i0}=L_i(N_{i0}/Q_{i0})\), whose polar factor is L_i. Also
\(M_{0j}/Q_{0j}=L_0(N_{0j}/Q_{0j})R_j\), whose polar factor is
\(L_0R_j\).

Thus (1) and (3) are mutually inverse continuous coordinates. They extract
q left U(2) factors and q - 1 right U(2) factors, contributing real dimension

\[
4q+4(q-1)=8q-4.
\tag{4}
\]

This construction uses the matrix M itself and does not require a continuous
choice of an original GS factorization.

## 3. What normalization does to every GS factorization

Suppose
\(M_{ij}=U_i\operatorname{diag}(A_{ij},B_{ij})V_j\).
Anchor invertibility implies that both central entries at each anchor are
nonzero. Write

\[
e_i=\operatorname{phase}(A_{i0}/Q_{i0}),\qquad
f_j=\operatorname{phase}(A_{0j}/Q_{0j}),
\]

and define the analogous phases for B. Denote the corresponding diagonal
two-by-two unitary matrices by \(E_i,F_j\). In particular, \(E_0=F_0\).
Polar covariance gives

\[
L_i=U_iE_iV_0,\qquad
R_j=V_0^*E_0^*F_jV_j.
\]

Consequently

\[
N_{ij}=V_0^*
\operatorname{diag}(a_{ij},b_{ij})V_0,
\qquad
a_{ij}=\overline{e_i}A_{ij}\overline{f_j}e_0,
\tag{5}
\]

with the analogous formula for b. These operations multiply the central
matrices by diagonal unitary matrices on both sides, so a and b are unitary.
Their anchor ratios are positive real numbers:

\[
a_{i0}/Q_{i0},\ a_{0j}/Q_{0j},\
b_{i0}/Q_{i0},\ b_{0j}/Q_{0j}\in\mathbb R_{>0}.
\tag{6}
\]

Define the dephased slice

\[
\mathcal D_Q=\{a\in U(q):
a_{i0}/Q_{i0},\ a_{0j}/Q_{0j}\in\mathbb R_{>0}
\text{ for all anchors}\}.
\]

We have proved that every normalized member of the full GS family has the
form

\[
N_{ij}=S\operatorname{diag}(a_{ij},b_{ij})S^*,
\quad a,b\in\mathcal D_Q,\quad S\in U(2).
\tag{7}
\]

Conversely, every matrix in (7) satisfies (2), is a GS matrix, and is fixed by
the normalization. Therefore (7) describes the entire normalized family,
not merely a selected subset or its tangent cone.

## 4. The dephased slice has dimension (q - 1) squared

On U(q), take the q first-column and q - 1 remaining first-row real
constraints

\[
\Phi(a)=\left(
\operatorname{Im}(a_{i0}/Q_{i0}),
\operatorname{Im}(a_{0j}/Q_{0j})_{j\ne0}
\right).
\]

At Q, use the tangent variations

\[
a(t)=\operatorname{diag}(e^{it\alpha_i})\,
Q\,\operatorname{diag}(e^{it\beta_j}),\qquad\beta_0=0.
\]

Their constraint derivatives are

\[
D\Phi_Q(a'(0))=
\bigl((\alpha_i)_i,(\alpha_0+\beta_j)_{j\ne0}\bigr).
\tag{8}
\]

This map is onto: given target coordinates u_i and v_j, choose
\(\alpha_i=u_i\) and \(\beta_j=v_j-u_0\). Hence the real implicit
function theorem makes \(\Phi^{-1}(0)\) a smooth submanifold near Q of
dimension

\[
\dim_{\mathbb R}U(q)-(2q-1)=q^2-2q+1=d.
\]

The positivity conditions in (6) hold on an open neighbourhood of Q in
this level set. We may therefore choose a smooth local coordinate map

\[
\psi:B_{3\varepsilon}(0)\subset\mathbb R^d
\longrightarrow\mathcal D_Q,
\qquad \psi(0)=Q,
\tag{9}
\]

which is a homeomorphism onto an open neighbourhood of Q in the slice.
This argument requires no assumption about the regularity of the map
\(a\mapsto(|a_{ij}|^2)\), sometimes called the unistochastic map.

## 5. The two-sphere and the exact fibres

The traceless Hermitian involutions of size two are

\[
H(n)=
\begin{pmatrix}
n_3&n_1-in_2\\
n_1+in_2&-n_3
\end{pmatrix},
\qquad n=(n_1,n_2,n_3)\in S^2.
\tag{10}
\]

Every one is unitarily conjugate to \(\operatorname{diag}(1,-1)\), and
every such unitary conjugate has this form.

For a and b in the chart (9), put

\[
c=\tfrac12(\psi^{-1}(a)+\psi^{-1}(b)),\qquad
z=\tfrac12(\psi^{-1}(a)-\psi^{-1}(b)).
\]

Then (7) becomes

\[
F(c,z,n)_{ij}
=\frac{\psi(c+z)_{ij}+\psi(c-z)_{ij}}2I_2
+\frac{\psi(c+z)_{ij}-\psi(c-z)_{ij}}2H(n).
\tag{11}
\]

For two triples in this coordinate domain,

\[
F(c,z,n)=F(c',z',n')
\quad\Longleftrightarrow\quad
c=c'\ \text{ and }\ nz^T=n'(z')^T.
\tag{12}
\]

Here is a proof covering the degenerate fibre z = 0. Block traces first
recover the entire matrix \(a+b\). If all traceless blocks vanish, then
a = b, so z = 0 by injectivity of \(\psi\). Equality of the two matrices
also forces \(z'=0\), and the scalar blocks recover c = c'. Both sphere
coordinates are then immaterial.

Otherwise select a block with coefficient \(t=(a_{ij}-b_{ij})/2\ne0\).
The equality of its traceless parts is

\[
tH(n)=t'H(n').
\]

It forces \(t'\ne0\) and \(H(n')=\lambda H(n)\). Hermitian symmetry
forces the complex scalar \(\lambda\) to be real. Squaring both sides
and using \(H(n)^2=H(n')^2=I_2\) gives \(\lambda=\pm1\).
All block coefficients therefore agree with the same sign. The recovered
pair of central matrices is either (a,b) or (b,a). Applying \(\psi^{-1}\)
gives respectively (c',z',n') = (c,z,n) or (c,-z,-n).

Finally, for unit vectors n and n', equality of the nonzero real outer
products \(nz^T=n'(z')^T\) has exactly this simultaneous-sign ambiguity.
This proves both directions of (12).

## 6. A homeomorphism of actual neighbourhoods

Let

\[
K=\{(c,z,n):\|c\|\le\varepsilon,
\ \|z\|\le\varepsilon,\ n\in S^2\}.
\]

This is compact, and c + z and c - z lie in the domain (9). The continuous
map

\[
G(c,z,n)=(c,nz^T)
\]

has image

\[
T=\{(c,W):\|c\|\le\varepsilon,
\ W\in\mathcal C_{3,d},\ \|W\|_F\le\varepsilon\}.
\tag{13}
\]

Indeed, a nonzero real matrix of rank one is a real outer product, and one
may normalize its first factor to unit length; then
\(\|nz^T\|_F=\|z\|\). The zero matrix is obtained with z = 0.

By (12), F and G have identical fibres on K. The continuous surjection
G from compact K onto Hausdorff T is closed, hence is a quotient map.
Consequently F descends to a continuous bijection

\[
\overline F:T\longrightarrow I:=F(K).
\]

Both T and I are Hausdorff, and T is compact. Thus this is a homeomorphism,
taking (0,0) to X.

It remains essential to prove that I contains a neighbourhood in the
**full** normalized GS family. Let N in that family approach X. For every
representation (7), the eigenvalues of its block N_ij are a_ij and b_ij.
Unitary diagonalization gives the uniform bounds

\[
|a_{ij}-Q_{ij}|, |b_{ij}-Q_{ij}|
\le\|N_{ij}-Q_{ij}I_2\|_{\mathrm{op}}.
\tag{14}
\]

Consequently both cores a and b approach Q, independently of the common
diagonalizing unitary. For N sufficiently close to X they belong to the
chart (9), and their inverse chart coordinates have norm less than
\(\varepsilon/2\). The resulting c and z have norm less than
\(\varepsilon/2\), so N belongs to I. This proves the required full
neighbourhood coverage.

The compact set T also contains an open neighbourhood of (0,0) in
\(\mathbb R^d\times\mathcal C_{3,d}\). To obtain open rather than merely
compact neighbourhoods, choose an open neighbourhood V of X in the
normalized family with V contained in I. The set

\[
\overline F^{-1}(V)\cap
\{(c,W):\|c\|<\varepsilon,\ \|W\|_F<\varepsilon\}
\]

is open in \(\mathbb R^d\times\mathcal C_{3,d}\), contains (0,0), and
its image is open in the normalized family. Restrict \(\overline F\)
to this set. Combining the resulting homeomorphism with the polar
coordinates (1)--(3) and local coordinates on
\(U(2)^{2q-1}\) proves the theorem.

This establishes an actual local homeomorphism. A description of a tangent
cone alone would not establish the theorem.

## 7. The singular link and the topological consequence

Assume q > 2, so d = (q - 1) squared is at least four. The unit Frobenius
link of the rank-one cone is

\[
L_{3,d}=\mathcal C_{3,d}\cap S^{3d-1}
\cong (S^2\times S^{d-1})/
\bigl((n,v)\sim(-n,-v)\bigr).
\tag{15}
\]

The map to the link is \((n,v)\mapsto nv^T\). It is onto, has exactly
the displayed two-element fibres, and induces a homeomorphism by compactness.
The diagonal antipodal action is free. Its quotient map is a two-sheeted
covering; since both spheres are simply connected for d >= 3, it is the
universal covering. Thus

\[
\pi_1(L_{3,d})\cong\mathbb Z/2,
\qquad
H_1(L_{3,d};\mathbb Z)\cong\mathbb Z/2.
\tag{16}
\]

The latter equality uses the degree-one Hurewicz theorem, namely that first
singular homology is the abelianization of the fundamental group.

The cone is contractible, and its punctured version retracts radially onto
the link. The long exact sequence of the pair therefore gives

\[
H_k(\mathcal C_{3,d},\mathcal C_{3,d}\setminus\{0\};\mathbb Z)
\cong\widetilde H_{k-1}(L_{3,d};\mathbb Z).
\]

Adding the Euclidean factor shifts local homology by s:

\[
H_k\left(\mathbb R^s\times\mathcal C_{3,d},
(\mathbb R^s\times\mathcal C_{3,d})\setminus\{(0,0)\};\mathbb Z\right)
\cong\widetilde H_{k-s-1}(L_{3,d};\mathbb Z).
\tag{17}
\]

For clarity, (17) is the relative cross-product calculation for the product
of the pairs \((\mathbb R^s,\mathbb R^s\setminus\{0\})\) and
\((\mathcal C_{3,d},\mathcal C_{3,d}\setminus\{0\})\), followed by
excision. The first relative homology is a free copy of the integers in
degree s only, so there are no additional Tor terms. Equivalently, the
punctured product retracts onto \(S^{s-1}*L_{3,d}\), and joining with
\(S^{s-1}\) shifts reduced homology by s.

Combining (16) and (17) yields the concrete local invariant

\[
H_{s+2}\left(\mathcal F_q,
\mathcal F_q\setminus\{X\};\mathbb Z\right)
\cong\mathbb Z/2.
\tag{18}
\]

Here local excision transports the calculation through the open-neighbourhood
homeomorphism proved above. A point of an n-dimensional topological manifold
without boundary has integer local homology equal to the integers in degree
n and zero in every other degree. The torsion group in (18) contradicts
this for every n.

**Corollary, as an ordinary mathematical theorem.** For every q > 2,
the unitary three-factor family \(\mathcal F_q\) is not a topological
manifold at the explicit point X above. This also excludes a manifold with
boundary, since all local homology groups at a boundary point are zero.

This conclusion is stronger than failure of embedded differentiable
smoothness. It follows from the proved local model and its local homology,
not from the corresponding real counterexample. The local-homology
calculation remains to be formalized in Lean. The actual full-family local
homeomorphism is now formalized, and the odd-q topological conclusion also
has the independent formal proof described below.

## 8. Dimension checks and the q = 2 boundary case

The regular nonzero part of \(\mathcal C_{3,d}\) has dimension d + 2.
Hence the local regular dimension of the full family is

\[
s+d+2=2q^2+4q.
\]

The ambient real dimension of U(2q) is \(4q^2\). The linear span of the
normal rank-one cone has dimension 3d, and

\[
s+3d=4q^2.
\]

For q = 2 one has d = 1, so \(\mathcal C_{3,1}=\mathbb R^3\).
The local model is ordinary Euclidean space of dimension 16. Accordingly,
the topological obstruction above starts at q > 2, as required. This is
consistent with the unitary cosine-sine decomposition for the q = 2 case.

## 9. The certified compact normalization and odd-q obstruction

The Lean proof of the full local model uses the same mathematical coordinates,
but avoids a separately formalized continuous polar-factor function. It
parametrizes all outer factors together with the compact central box.
Positive polar-factor uniqueness recovers both outer tuples from each matrix;
the exact central fibre theorem recovers (c, nz^T). The two compact maps
therefore have identical fibres and induce a homeomorphism of their images.
`TopologyFullImage.lean` proves this full quotient statement.

Every model point is feasible in the original family. Conversely, use the
compact space of all original unitary factorizations. Every representative
of the scalar-block base has nonzero anchors, identity normalized outer
factors, and both dephased cores equal to Q. Continuity of dephasing and the
actual inverse chart gives an open set containing this entire fibre on which
both cores have small coordinates. Its matrices lie in the compact model.
The image of the compact complement is closed and misses the base. Its
complement is therefore an ambient open neighbourhood whose intersection
with the full original family is covered. This is the theorem in
`FullCoverage.lean`; it does not select one factor branch.

`TopologyNeighbourhood.lean` and `MatrixNonmanifold.lean` assemble these facts
into the actual pointed neighbourhood model. `LocalTransport.lean` restricts
the neighbourhood model to open neighbourhoods, uses actual Cayley charts on
the outer factors, and absorbs the free real coordinates.

For odd q >= 3, d = (q-1)^2 is a positive multiple of four. Regard R^d as
blocks of four real coordinates. Choose orthogonal complex structures I and
J on these blocks with IJ = -JI. For a rank-one matrix W = uz^T, ||u|| = 1,
define the linear contraction

\[
T(W)=(u_0\operatorname{id}+u_1 I+u_2 J)z.
\]

This is linear in the entries of W, so it is independent of its outer-product
presentation. Anticommutation gives ||T(W)||^2 = ||W||_F^2. The section which
places z in the first row satisfies T(section(z)) = z. Thus T vanishes only
at the vertex and gives an actual Euclidean retract. With an e-dimensional
free factor, every punctured vertex neighbourhood admits a sphere retract
of dimension e+d-1.

The certified sphere-dimension theorem forces a hypothetical vertex chart
to have dimension e+d. Every such neighbourhood also meets the nonzero
rank-one locus, where the explicit pivot chart has dimension e+d+2. The
certified equality of dimensions of overlapping charts is a contradiction.
These are actual topological charts; no differentiability hypothesis is
used. The key modules are `QuaternionRetraction.lean`, `EuclideanRetract.lean`,
`RegularChart.lean`, `Nonmanifold.lean`, and `LocalTransport.lean`.

Finally, `MatrixNonmanifold.lean` applies this obstruction to the full
scalar-indexed family using the proved local model. It also embeds the
existing explicit real Householder base as a unitary matrix, so the
singular-point existence theorem has only the integer hypotheses q >= 3
and Odd q. This closes the topological result for odd q without importing
the unformalized homology proof for even q.
