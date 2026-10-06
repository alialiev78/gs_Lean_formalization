# Two-factor orthogonal geometry with arbitrary overlap

`GS.OverlapGeometry` constructs a smooth manifold structure for the original
two-factor family with **independent orthogonal blocks**, allowing arbitrary
overlap of the two support patterns after permutation. The topology is the
inherited topology of the matrix set. The construction handles a
positive-dimensional stabilizer and does not require a locally injective map
from all factor coordinates.

The main conclusions are:

- `overlapIsManifold`: a smooth atlas on the actual matrix orbit.
- `inA2Orth_admits_manifold`: the statement for the original scalar-indexed
  `InA2Orth` family.
- `overlap_val_contMDiff` and `overlap_val_mfderiv_injective`: smooth inclusion
  into matrices and injectivity of its actual manifold differential.
- `orbit_tangent_image_iff` and `pointProjection_unique_tangent_lift`: the
  actual tangent image and unique intrinsic lift of the point-only projector.
- `tangentPairing_pos`, `tangentMetricExtension_contMDiff`, and
  `tangentEnergy_contMDiff`: a positive Frobenius metric and smooth evaluation
  on the genuine tangent bundle.
- `intrinsicGradient_characterization` and `intrinsicGradient_unique`: the
  actual intrinsic gradient for differentiable restricted ambient losses.
- `cayleyRetraction_contMDiff`: a smooth retraction on the whole actual tangent
  bundle, with its zero-section and identity fibre-differential theorems.
- `cayleyTangentStep_armijo` and `cayley_backtracking_terminates`: intrinsic
  descent and finite geometric backtracking for differentiable losses.

All names above are in `GS.OverlapGeometry`.

## The orbit and its topology

Let `K₁` and `K₂` be the compact groups of orthogonal matrices supported by the
two specified block-label maps. Their product acts by

\[
(L,R)\cdot X=LXR^{\mathsf T}.
\]

For a permutation matrix `P`, its orbit is the same set as the corresponding
orthogonal two-factor family. Transposing the right factor preserves both its
support and orthogonality. `orbit_set_eq_inA2Orth` proves the exact scalar-block
identification.

The existing `GS.LieAction.quotientOrbitHomeomorph` identifies the topological
quotient by the stabilizer with this matrix orbit. Compactness of the factor
group and the Hausdorff matrix topology justify this identification. The orbit
map is open: the inverse image of the image of an open set is its union of
translates by stabilizer elements. This argument uses the original subtype
topology throughout.

## Separating the kernel

The factor Cayley chart is written `κ`. At the identity, with supported skew
coordinates `(C, Ω)`, the derivative of the orbit parametrization is

\[
D(C,\Omega)=-2CP+2P\Omega.
\]

Its kernel therefore consists exactly of pairs satisfying `CP = PΩ`.
Choose a linear complement `H` of `ker D` in the finite-dimensional factor
coordinate space. The complement need not be orthogonal: it is used as a
coordinate model, and the metric is constructed separately.

`KernelCayley.lean` proves that every kernel vector integrates to an actual
stabilizer element. The identity `CP = PΩ` implies

\[
\operatorname{cay}(C)P=P\operatorname{cay}(\Omega),
\qquad
\operatorname{cay}(C)P\operatorname{cay}(\Omega)^{\mathsf T}=P.
\]

The supported skew hypotheses ensure that the Cayley inverses exist. Thus
kernel coordinates leave the orbit point unchanged, not merely unchanged to
first order.

## The two inverse-function arguments

First consider multiplication of factor lifts, expressed back in factor
coordinates:

\[
\Psi(h,k)=\kappa^{-1}\bigl(\kappa(h)\kappa(k)\bigr),
\qquad h\in H,\quad k\in\ker D.
\]

Its derivative at zero is `(h,k) ↦ h+k`, a linear equivalence by construction
of the complement. The inverse-function theorem supplies a local product
chart. The source is restricted so that the inverse Cayley coordinates really
reconstruct the product. Since `κ(k)` stabilizes `P`, the orbit image of this
product depends only on `h`.

Second, define the horizontal slice `φ(h) = κ(h) · P`. The restriction of `D`
to `H` is injective. Finite-dimensional linear algebra constructs a continuous
linear map `A` on the whole ambient matrix space such that

\[
A\circ D|_H=\operatorname{id}_H.
\]

The map `h ↦ A(φ(h)−P)` has derivative the identity at zero. A second
inverse-function theorem gives an ambient smooth coordinate map `c` satisfying
`c(φ(h)) = h` on an open neighbourhood of zero.

This supplies a smooth local inverse to the slice. Its image must still be
proved open in the entire orbit. The first product chart and the open orbit
map supply exactly that step: an open horizontal domain, together with its
local stabilizer coordinates, has the same orbit image as the horizontal slice.
No relative-openness hypothesis is left unproved.

## Atlas, tangent differential, and metric

The resulting slice is a partial homeomorphism between a relatively open
subset of the actual orbit and an open subset of `H`. Translate it by the
factor-group action to cover every orbit point. A transition map is the
ambient smooth coordinate map of one slice composed with the ambient smooth
parametrization of the other, hence is smooth.

Choosing a preferred factor representative for each chart centre does not
require a continuous choice of representatives. Smoothness is proved for each
fixed chart and every transition map. The original matrix-subtype topology is
retained. `SmoothMaps.lean` also proves a useful converse to smoothness of the
inclusion: a map from a real normed space into this slice manifold is smooth
if and only if its ambient matrix-valued realization is smooth. This criterion
uses the ambient coordinate maps and needs no smoothly chosen factors.
`ManifoldSmoothMaps.lean` extends the criterion to arbitrary manifold sources,
which permits its application to the actual tangent bundle.

Differentiating the local inverse identities proves that the manifold
differential of the inclusion into matrices is injective.
`horizontalOrbit_fderiv_zero_range` additionally shows that discarding the
kernel preserves the complete `TwoFactorDirection` image of the factor
derivative, including after translation to any point.

For actual tangent vectors `v,w` at `X`, define

\[
g_X(v,w)=\langle d\iota_X(v),d\iota_X(w)\rangle_F.
\]

Injectivity of `dι` proves positive definiteness. Smoothness of the tangent map
of the inclusion and of the ambient Frobenius pairing proves smooth metric
evaluation on the total tangent bundle. The construction retains the original
chart norm; it does not silently identify that norm with the Frobenius norm.

`TangentBridge.lean` identifies the actual inclusion-differential image with
`TwoFactorDirection`. The point-only orthogonal projector therefore has a
unique lift to the true tangent fibre and satisfies its Frobenius least-squares
identity against every actual tangent vector.

For an ambient loss differentiable at `X`, `Gradient.lean` proves the manifold
chain rule for its restriction. Projecting the ambient Frobenius gradient and
lifting it to the tangent fibre gives the unique vector satisfying

\[
g_X(\operatorname{grad}f,v)=d(f|_M)_X(v).
\]

The intrinsic gradient vanishes exactly when the restricted manifold
derivative vanishes. Its metric square equals the Frobenius square of the
ambient projected gradient. No equality with the norm of its horizontal
coordinates is asserted.

## Retraction and intrinsic descent

`Retraction.lean` lifts the existing point-only Cayley update to actual tangent
vectors of this atlas. At a fixed base point X, the resulting map R_X is smooth,
satisfies R_X(0)=X, and has actual manifold differential dR_X(0)=id. The
time-parametrized update has the prescribed initial tangent velocity.

`BundleRetraction.lean` proves the stronger joint statement: R is a smooth map
from mathlib's actual tangent bundle to the orbit. Its ambient value depends
only on X and the included tangent vector dι_X(v), through the globally smooth
point-only Cayley formula. Combining smoothness of this tangent inclusion with
the arbitrary-source ambient criterion proves joint smoothness without a
smoothly varying choice of factor representatives.

`Descent.lean` applies the restricted-loss chain rule to the negative intrinsic
gradient. A differentiable loss decreases with derivative minus the squared
metric norm at time zero. For a nonzero gradient, any Armijo constant in (0,1)
is satisfied by all sufficiently small positive steps; geometric backtracking
with positive initial step and ratio in (0,1) terminates. No global convergence
or rate follows from these local statements. See [RETRACTIONS.md](RETRACTIONS.md).

## Geodesic and connection components

`GeodesicDynamics.lean` differentiates moving factor velocities and identifies
the projected acceleration with the generator residual S' + Π[C,K].
`GeodesicEnergy.lean` proves constant Frobenius energy under the stated actual
generator ODE. `GeodesicConnection.lean` constructs projected second derivatives
of inverse charts, proves symmetry of these Christoffel coefficients, and
proves coordinate and along-curve metric compatibility. These are actual
differential statements, but they do not register a global bundled
Levi-Civita connection.

The no-overlap case now has a completed explicit matrix-orbit construction in
`GS/Geodesics/OrbitBlock.lean`. Its curve `L exp(tC) P exp(tΩ) R` is smooth in
this actual horizontal atlas. Its first and second matrix derivatives are
proved, and the first derivative is exactly the inclusion image of the true
manifold curve velocity. The established `covariantAlong` operation applied
to that velocity vanishes for all real times. Every actual initial tangent
vector is realized, and the Frobenius speed is constant.
`OrbitShuffle.lean` proves the result for the original scalar permutation
under `k₁ ≥ b₂`, explicitly recording the regular dimension equalities.
Here `k₁` counts right-layer blocks; it is not their size.
See [BLOCK_GEODESICS.md](BLOCK_GEODESICS.md) for the proof and API.

The bracket and balanced-generator modules in `GS/Geodesics/` prove the support
and residual identities behind the all-overlap dynamics. The complete
three-exponential integration is proved in the mathematical text
[ORTHOGONAL_GEODESICS.md](ORTHOGONAL_GEODESICS.md), including its unitary
analogue. That full integration and a global geodesic flow are not yet
Lean-certified.

## Scope and remaining interfaces

This construction concerns two independent real orthogonal factor layers,
arbitrary finite block-label maps, and arbitrary permutation connectors. It
also covers continuous stabilizers and the zero-dimensional cases. It does not
assert a manifold theorem for all three-factor families, which have separate
singularity examples.

`GS.ManifoldCompletion` and `GS.RiemannianCompletion` use explicit
nonoverlap assumptions. The tangent, projection, metric, gradient, retraction
and descent interfaces in `GS.OverlapGeometry` use the arbitrary-overlap
atlas. Each theorem retains the hypotheses of its own construction.

Physical sharing has separate algebraic projection, coupled normal-equation,
factor-velocity and feasible descent results. `GS.SharedGeometry` supplies
a complete-block orthogonal orbit atlas, actual
tangent bridge, local factor sections and image-curve lifting, physical metric,
smooth projector and minimum-norm lift, canonical whole-bundle retraction,
intrinsic descent and smooth gradient section. Cross-layer ties and partial-block
constraints are separate extensions. The complex two-factor atlas is constructed in
`GS.UnitaryManifold`, including its unavoidable phase kernel in the stabilizer
coordinates. See [UNITARY_MANIFOLD.md](UNITARY_MANIFOLD.md).

## Source order

1. `HorizontalModel.lean`: complements and the ambient linear left inverse.
2. `KernelCayley.lean`: kernel integration to the stabilizer.
3. `LocalProduct.lean`: factor multiplication and the product IFT.
4. `ProjectedSlice.lean`: the ambient smooth coordinate map.
5. `FactorChartOpen.lean`: open factor maps and open slice images.
6. `SliceAtlas.lean`, `OrbitAtlas.lean`: the actual atlas and inclusion differential.
7. `HorizontalDifferential.lean`: the complete generator image on the horizontal model.
8. `TangentBridge.lean`: actual tangent image and intrinsic projection.
9. `Riemannian.lean`: the smooth positive metric on actual tangent fibres.
10. `Gradient.lean`: restricted-loss differential and unique intrinsic gradient.
11. `SmoothMaps.lean`, `ManifoldSmoothMaps.lean`: ambient criteria for normed-space
    and arbitrary manifold sources.
12. `Retraction.lean`, `BundleRetraction.lean`: actual tangent-fibre identities
    and a smooth map on the entire tangent bundle.
13. `Descent.lean`: intrinsic Cayley Armijo descent and finite backtracking.
14. `GeodesicDynamics.lean`, `GeodesicEnergy.lean`: moving generators, actual
    acceleration, projected residual, and constant energy.
15. `GeodesicConnection.lean`: symmetric local connection coefficients and
    metric-compatibility identities.
16. `GS/Geodesics/ShuffleCondition.lean`, `OrbitBlock.lean`, `OrbitShuffle.lean`:
    exact scalar-shuffle convention and block geodesics in the actual matrix
    orbit through every initial tangent under no-overlap.
