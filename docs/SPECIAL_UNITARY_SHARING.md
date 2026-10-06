# Special-unitary sharing

**Experimental:** the 36 source modules under
`experimental/special_unitary/GS/SpecialUnitarySharing` are unfinished and
excluded from the supported build. The statements described below are intended
interfaces, not established results of the supported library.

This construction imposes **determinant one on every physical block**.
Sharing repeats complete blocks within a layer. Positive block sizes divide
the ambient size; layer sizes, labels and multiplicities may differ, and the
fixed carrier may be singular or zero.

## The essential difference from U

For a unique block of size b, the infinitesimal model is

\[
\mathfrak{su}(b)=\{A:A^*=-A,\ \operatorname{tr}A=0\}.
\]

The trace condition is applied separately to each physical block. For example,
`diag(i,-i)` has total trace zero, but it is not a generator for two scalar
SU(1) blocks. Likewise, cancellation of determinants in different blocks does
not make those blocks individually special unitary.

The existing normalized Cayley transform cannot be reused in general. With

\[
A=\operatorname{diag}(i,i,-2i),\qquad c_1(A)=(I+A/2)(I-A/2)^{-1},
\]

one has

\[
\det(I+A/2)=7/4+i/4,\quad \det(I-A/2)=7/4-i/4,
\quad \det c_1(A)=24/25+7i/25\ne1.
\]

`Regression.cayley_does_not_preserve_SU3` gives a Lean proof body for this
counterexample, using the existing exact Cayley multiplication identity.
The replacement in this extension is the ordinary matrix exponential.

## Actual groups and topology in the source

`BlockAlgebra.lean` extracts a physical block from an actual ambient row anchor.
All anchors are checked, so duplicate anchors simply repeat the same condition.
`BlockTraceZero` and `BlockDetOne` are literal trace and determinant conditions.

`Algebra.lean` defines the closed determinant kernels inside the existing
unitary shared factor group. Multiplication, inversion and compactness are
proved from those literal conditions. It also proves a useful stronger fact:
the SU generator spaces are normalized by the **larger** U-sharing group.

`Orbit.lean`, in the namespace `GS.SpecialUnitarySharing.Orbit`, constructs
the genuine SU group action and orbit, its compactness, and the homeomorphism
from the stabilizer quotient to the original matrix-subspace topology. Its
`MatrixOrbit` is NOT the U orbit. `toUnitaryOrbit` is only an inclusion.
The draft modules `FactorCharts` and `OrbitAtlas` implement separate manifold
structures for these SU factors and this smaller orbit. Their proof bodies
require successful compilation and axiom checking.

## Constructed local coordinates and the actual SU orbit atlas

The source does not assume a special-unitary manifold, a matrix logarithm, or
local lifting of an arbitrary image curve. The following construction supplies
those local geometric interfaces from the U-sharing infrastructure.

### Exponential coordinates without a global logarithm

Write E_s for the full shared skew-Hermitian model and F_s for its actual
blockwise trace-free subspace. Let c be the original U Cayley coordinate map
with derivative -1/2 at the identity. On E_s consider

\[
F(A)=c(\exp(-2A)).
\]

`ExponentialDifferential` proves the actual matrix-exponential derivative at
zero. `unitaryExpCoordinates_fderiv_zero` then proves
that D F(0) is the identity on E_s. The inverse function theorem constructs
an inverse kappa on open neighbourhoods of zero. These are genuine ambient
matrix coordinates followed by the already proved U-coordinate map, not a
newly declared differential.

Shrink the neighbourhood so every exponential is Cayley-admissible and each
physical trace -2 tr(A_j) lies in a scalar-exponential injectivity neighbourhood
of zero. That scalar neighbourhood is also constructed by the inverse function
theorem in the real vector space C. If the resulting physical block has
determinant one, then

\[
1=\det\exp(-2A_j)=\exp(-2\operatorname{tr}A_j),
\]

and LOCAL injectivity gives tr(A_j)=0. This proves that the inverse coordinates
of every nearby actual SU factor lie in F_s. It covers the entire subgroup
neighbourhood, not just an image of selected generators.

`factorPartialChart` has coordinates kappa(c(Q* M)), restricted
to the actual SU source, and reconstruction Q exp(-2A). Its target is an open
neighbourhood in F_s, NOT all of F_s. Reconstruction is globally defined, but
all inverse and openness lemmas explicitly require the local target condition.
The source proves `specialFactorIsManifold` and `specialFactorLieGroup`, with
the original matrix-subspace topology.

### A local horizontal slice with continuous stabilizers

For G=G_2^SU x G_1^SU acting by (L,R).X=L X R*, the actual derivative of the
factor chart at the identity is

\[
\delta_P(C,\Omega)=-2CP+2P\Omega.
\]

Let K=ker(delta_P), and choose a linear complement H. The product of exponential
reconstructions of h in H and k in K, written in the local factor coordinates,
has derivative (h,k) -> h+k. The inverse function theorem therefore gives a
local product chart. Its domain is further restricted to ensure that the
product factors lie inside the LOCAL inverse-coordinate source.

Only the implication

\[
CP=P\Omega\quad\Longrightarrow\quad
\exp(-2C)P\exp(2\Omega)=P
\]

is needed to remove the kernel factor. It is proved by passing intertwining
through the convergent exponential series. No false global converse for a
single finite exponential step is used. The all-real-time stabilizer
equivalence remains available separately in `Stabilizer`.

A linear left inverse to delta_P restricted to H, composed with the ambient
horizontal parameterization, has invertible derivative. A second inverse
function theorem gives a smooth ambient inverse on a small horizontal slice.
The original compact-group orbit map is open. Apply that open map only to
factor-coordinate images lying in the LOCAL exponential chart target. This
proves that the horizontal image is open in the WHOLE actual SU orbit.
Translating these slices yields `sharedOrbitChartedSpace`,
`sharedOrbitIsManifold`, and `inSharedA2SU_admits_manifold`.

### True tangent image and local factor sections

`orbit_tangent_image_iff` identifies the range of the genuine
`mfderiv` of the orbit inclusion with

\[
\operatorname{im}D_X,\qquad D_X(A,B)=AX+XB,
\quad A\in\mathfrak s_2^{SU},\ B\in\mathfrak s_1^{SU}.
\]

The inclusion differential is injective. This is not a definition of a new
surrogate tangent space. The carrier is an arbitrary fixed complex matrix,
including singular and zero carriers; ranks are only held constant on its
fixed orbit.

`LocalSections` constructs actual local smooth SU factor sections, and local
lifts of curves that are merely differentiable at a chosen parameter. A global
continuous or smooth selection of factors is not asserted.

## Physical metric, projector and canonical lift

All spaces are real vector spaces of complex matrices. The ambient metric is

\[
\langle Z,W\rangle_F=\operatorname{Re}\operatorname{tr}(Z^*W).
\]

On generator pairs use the sum of **full physical** Frobenius norms. A unique
block used m times therefore has weight m. This is implemented using an
auxiliary genuine L2 coordinate space, not by giving the existing matrix
supremum norm an incompatible inner-product instance.

Let Pi_X be the orthogonal projector onto im(D_X). The canonical lift is

\[
\Lambda_XZ=\mathop{\rm argmin}_{D_X(A,B)=\Pi_XZ}
          (\|A\|_F^2+\|B\|_F^2).
\]

The solution is the unique lift orthogonal to ker(D_X). The source constructs
it by finite-dimensional projection onto that kernel. It establishes

\[
\|w\|_{\rm phys}^2=\|\Lambda_XZ\|_{\rm phys}^2+
                      \|w-\Lambda_XZ\|_{\rm phys}^2
\]

for every other feasible w. No inverse of a possibly singular normal operator
is assumed.

The adjoint is

\[
D_X^*Z=(Q_2(ZX^*),Q_1(X^*Z)),
\]

where Q_i project onto the **blockwise trace-free, tied** generator spaces.
The complete normal equations D_X* D_X v = D_X* Z are equivalent to the full
least-squares problem. Overlap-only fitting and unweighted sharing averages
are not substituted for these equations.

The normalizing U-sharing action sends each SU generator space to itself and
preserves the physical norm. It follows that Pi_X and Lambda_X are equivariant
and their ranks are constant on each U orbit, not merely on its SU suborbit.
The U local sections give smooth extensions on the entire surrounding
U orbit, as explicitly named by `*_on_unitary_orbit`. `IntrinsicSmooth` now
proves that the inclusion of the separately charted SU orbit in the U orbit is
smooth, and restricts these extensions to the actual SU base. It does not
identify the two orbits or their tangent spaces. In particular,
`pointProjection_contMDiff` and `minimumNormLift_contMDiff` use the smaller SU
atlas. No smoothness across different carrier ranks is asserted.

For a single unique b x b block after averaging the tied occurrences, the
practical infinitesimal correction is

\[
H=(Z-Z^*)/2,\qquad H_0=H-\frac{\operatorname{tr}H}{b}I.
\]

The established single-block `tracelessPart` result is reused on **each**
extracted physical block in `Regression.blockTraceZero_iff_tracelessPart_fixed`.
An executable expanded sharing solver and its complexity are not formalized
by merely giving this local formula.

## Exponential update and first-order optimization

For (A,B)=Lambda_X Z define

\[
E(X,Z,t)=\exp(tA)X\exp(tB).
\]

Every physical block is unitary because its generator is skew-Hermitian, and
has determinant exp(t tr(A_block))=1. `ComplexExponential.lean` proves the
required skew-Hermitian determinant identity by Hermitian spectral reduction;
it does not assume a missing general `det_exp` theorem. `Exponential.lean`
passes the actual convergent series through block extraction and proves
physical SU feasibility.

The exact finite update is independent of normal input components, preserves
the genuine SU orbit for all real t, and satisfies

\[
E(X,Z,0)=X,\qquad \partial_tE(X,Z,0)=\Pi_X Z.
\]

`IntrinsicSmooth` proves that this update is jointly smooth both as a matrix
map on the actual SU base and as a map into the actual SU orbit. For a genuine
SU tangent vector v put V=d iota_X(v), and define

\[
R_X(v)=E(X,V,1).
\]

`Retraction` proves the actual manifold derivative, and `BundleRetraction`
defines `expRetraction` on the WHOLE mathlib SU tangent bundle, proves its
joint smoothness, and establishes

\[
R_X(0)=X,\qquad D(R_X)_0=\operatorname{id}_{T_X\mathcal S}.
\]

The term "exponential retraction" refers to the matrix exponentials in this
formula; it is not a theorem that this is the Riemannian exponential map.

`Riemannian` supplies the positive smooth pullback of the real Frobenius metric.
`Gradient` proves the intrinsic Riesz identity using the true inclusion
differential. `GradientSection` constructs the smooth tangent-bundle-valued
projection via the actual tangent map of (X,Z) -> R_X(tangentProjection_X Z),
avoiding an assumed smooth inverse to the inclusion differential. It yields
C^(r+1)-to-C^r regularity for the intrinsic gradient section and the exact
fixed-step gradient update, including the ordinary C-infinity case.

For a real differentiable objective the projected-gradient representative is
G_X=Pi_X(grad f(X)). The exact source curve E(X,-G_X,t) lies in the SU family
and has loss derivative -||G_X||_F^2 at zero. This gives strict Armijo descent
and finite geometric backtracking for G_X != 0. The `Descent` statements remain available without a manifold
assumption. The new `IntrinsicDescent` statements use the actual SU intrinsic
gradient, its induced metric, and the SAME whole-bundle `expRetraction`.
Geometric backtracking terminates for a nonzero gradient at a differentiable
loss point; no smoothness of the discrete step-selection rule is asserted.
Global convergence, rates, numerical exponentiation and momentum transports
remain separate assertions.

## Exact source map

All entries below are proof bodies pending elaboration and kernel audit.
The common namespace is `GS.SpecialUnitarySharing`, except for the explicit
`Orbit` and `Regression` subnamespaces.

| Assertion | Main declaration |
| --- | --- |
| Literal determinant-one factors, compact closed subgroups | `specialSubgroup`, `specialSubgroup_isClosed`, `specialFactorCompactSpace` |
| Exact SU orbit and quotient topology | `Orbit.orbit_iff_inShared`, `Orbit.quotientOrbitHomeomorph` |
| Actual one-parameter stabilizer equivalence | `pointMap_kernel_iff_exponential_stabilizes` |
| Lie closure | `commutator_special`, `spatialField_operator_commutator_mem` |
| Factor-independent direction space | `sharedDirection_factor_independent` |
| Full least-squares equivalence | `pointNormalEquation_iff_minimizes` |
| Canonical physical lift | `minimumNormLift_unique_minimizer` |
| Smooth extensions on the U orbit | `pointProjection_contMDiff_on_unitary_orbit`, `minimumNormLift_contMDiff_on_unitary_orbit` |
| Each exponential block is SU | `cMatrixExp_special`, `cExpLine_special` |
| Actual SU-orbit preservation | `expStep_in_family` |
| Normal input invariance | `expStep_projected`, `expStep_equal_projections` |
| Initial derivative and all generator directions | `expStep_hasDerivAt_direction`, `expStep_realizes_every_direction` |
| Continuity into the actual SU orbit | `orbitExpStep_continuous` |
| Feasible Armijo backtracking | `feasible_backtracking` |
| Smooth matrix gradient representative | `projectedGradient_smooth_on_unitary_orbit` |
| Regressions against incorrect U-to-SU transfers | `Regression.cayley_does_not_preserve_SU3`, `Regression.exists_nonzero_SU_synthesis_kernel` |

## Added intrinsic source interfaces

All names below are in `GS.SpecialUnitarySharing`. These are written proof
bodies pending elaboration and kernel audit, not externally assumed premises.

| Interface | Exact source role |
| --- | --- |
| `trace_zero_of_exp_one` | Scalar-exponential injectivity used only on its constructed local source |
| `traceFree_of_local_special_exp` | All physical logarithmic coordinates are trace-free near an actual SU factor |
| `specialFactorIsManifold`, `specialFactorLieGroup` | Actual SU factor atlas and smooth group structure |
| `factorLift_stabilizes_of_kernel` | The direction required by the local product, without a global exp-injectivity assumption |
| `horizontalChartImage_open` | Relative openness in the entire compact SU orbit |
| `inSharedA2SU_admits_manifold` | SU family in the original matrix topology |
| `orbit_tangent_image_iff` | Full image of the true inclusion differential |
| `exists_local_differentiable_factor_curve` | Local factor lifting is a conclusion |
| `toUnitaryOrbit_contMDiff` | Smooth inclusion, not identification, of SU and U orbits |
| `pointProjection_contMDiff`, `minimumNormLift_contMDiff` | Smoothness on the actual SU base |
| `orbitExpStep_contMDiff` | Smooth update valued in the actual SU orbit |
| `tangentMetricExtension_contMDiff` | Smooth positive Frobenius pullback metric on the true tangent bundle |
| `expRetraction_contMDiff`, `expRetraction_fibre_mfderiv_zero` | Canonical whole-bundle retraction and genuine identity differential |
| `intrinsicGradientSection_contMDiff_of_order` | C^(r+1)-to-C^r regularity of the actual gradient section |
| `expRetraction_backtracking_terminates` | Intrinsic finite backtracking using that same retraction |

## Remaining work and scope

The SU atlas, tangent bridge, retraction and gradient interfaces require
compilation repair and complete validation. The O/U dependencies belong to
the supported library; this draft does not extend their verification scope.

General SU/unitary geodesics, an abstract global Levi-Civita connection,
certified numerical exponentiation/AD/solvers, optimizer convergence or rates,
and partial-block or cross-layer ties are separate tasks. The full geometric
construction here concerns repetition of whole SU blocks within each of two
layers. It never replaces per-block determinant one by a total determinant
constraint, or the physical metric by unweighted unique-block coordinates.
