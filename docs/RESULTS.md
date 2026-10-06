# Result index and exact scope

This index separates proved theorems from definitions of desired propositions
and from conditional alternative arguments. Names below refer to Lean
declarations, not informal manuscript numbering. The full types are the
authoritative statements. [VERIFICATION.md](VERIFICATION.md) explains how to
build the library and audit proof dependencies.

## Algebraic factorization

All names in the proof column are fully qualified.

| Specification or statement | Proof | Scope |
| --- | --- | --- |
| `GS.Specifications.TwoFactorOrthogonalizationGoal` | `GS.Extensions.twoFactorOrthogonalization` | Actual real matrices; arbitrary permutation; a valid `BlockSpec` for each factor |
| `GS.Specifications.ThreeFactorOrthogonalizationGoal` | `GS.Extensions.threeFactorOrthogonalization` | Three factors with independently specified block sizes and two arbitrary permutations |
| `GS.Specifications.StructuredQRGoal` | `GS.Extensions.structuredQR` | Block-supported invertible input; orthogonal supported factor and upper-triangular remainder |
| `GS.Specifications.StructuredRQGoal` | `GS.Extensions.structuredRQ` | Right-sided counterpart |
| `GS.Specifications.CholeskySupportGoal` | `GS.Extensions.choleskySupport` | Support of a triangular Gram factor; not an identification with a symmetric square root |
| `GS.Revision.Specifications.ThreeFactorUnequalBlocksGoal` | `GS.Revision.Specifications.threeFactorUnequalBlocks` | General block labels; the middle label map must be monotone |
| `GS.Specifications.FourFactorCounterexampleGoal` | `GS.Specifications.fourFactorCounterexample_draft` | Explicit orthogonal `6 × 6` matrix in the unrestricted four-factor family but not its orthogonal-factor subfamily |
| `GS.Specifications.FourFactorNecessaryConditionGoal` | `GS.Specifications.fourFactorNecessaryCondition_draft` | Ratio inequality with the stated nonzero-denominator hypothesis |
| `GS.Revision.Specifications.FourFactorPolynomialGoal` | `GS.Revision.Specifications.fourFactorPolynomial` | Polynomial inequality without a denominator hypothesis |
| Strict inclusion of four-factor orthogonal families | `GS.Results.Algebra.fourFactorStrictInclusion` | Set-level consequence of the explicit counterexample; same `6 × 6` family and permutation |
| Exact block-rank criterion for a supported two-factor product | `GS.Results.CellRank.global_iff_block_rank` | A factorization exists if and only if every output block has rank at most the number of its intermediate cell slots; empty cells are included |
| Block-rank criterion for the original matrix family | `GS.Results.OriginalCellRank.inA2_iff_block_rank` | Exact `InA2 b₁ b₂ (permMatrix σ) A` statement for arbitrary permutations; each zero-padded output block has rank at most its cell cardinality |

The declarations ending in `_draft` are proved theorems. Their public wrappers are in
[`GS/Results/Algebra.lean`](../GS/Results/Algebra.lean).

The four-factor proof also gives a strictly negative obstruction value at the
counterexample (`GS.Revision.M4.value_at_Q`) and an open neighbourhood excluded
from the orthogonal-factor family (`GS.Revision.M4.open_exclusion_neighborhood`).
These are exact symbolic statements, not floating-point experiments.

The block-rank criterion characterizes membership after
`GS.Revision.Cells.global_iff_independent`. It proves existence of each local
rank factorization and then glues the supported factors. Local row/column
coordinate sets and the intermediate slot set are finite. It concerns
unrestricted real supported factors; orthogonality is a separate property.
`OriginalCellRank.inA2_iff_block_rank` transports this characterization to the
original scalar-indexed `InA2` definition, with no supplied factorization
witness or matrix invertibility assumption.

## Cosine-sine decomposition

| Result | Declaration | Scope |
| --- | --- | --- |
| Complete square real CS decomposition | `GS.Results.CosineSine.square` | Every orthogonal matrix on `Fin p ⊕ Fin p`; four orthogonal outer blocks and angles in `[0, π/2]`, including all degeneracies |
| Exact original-family exhaustion over the real field | `GS.Results.CosineSine.scalar_exhaustion`, `GS.Results.CosineSine.scalar_family_eq_orthogonal` | `InA3Orth p 2 p P Pᵀ M ↔ Orthogonal M`, where `P = permMatrix (scalarShuffle 2 p)`; every `p`, including zero |
| Complete square complex CS decomposition | `GS.Results.UnitaryCosineSine.square` | Every complex unitary matrix on `Fin p ⊕ Fin p`; four unitary outer blocks and real angles in `[0, π/2]`, including zero/unit and repeated singular values |
| Exact original-family exhaustion over the complex field | `GS.Results.UnitaryCosineSine.scalar_exhaustion`, `GS.Results.UnitaryCosineSine.scalar_family_eq_unitary` | `CInA3Unitary p 2 p P Pᴴ M ↔ Unitary M`, with the exact `scalarShuffle 2 p`; every `p`, including zero |

The [CS proof guide](CS_DECOMPOSITION.md) explains column completion, the spectral
step, the exact scalar-shuffle bridge, and why this exhaustion statement is
stronger than applying three-factor orthogonalization to an already given
factorization. The [unitary CS guide](UNITARY_CS.md) gives the complete complex
proof and distinguishes `(p,2,p)` exhaustion from the `(2,q,2)` local-model
problem.

## Local model and topological obstruction

| Statement | Proof | Hypotheses and conclusion |
| --- | --- | --- |
| Equality of the original parametrization fibres on a uniformly small compact domain | `GS.Continuation.originalSameFibres` | Exact type `GS.Specifications.OriginalSameFibresGoal` |
| Coverage of the original local family, not only a selected parametrized branch | `GS.NonmanifoldCompletion.originalLocalCoverage` | Exact type `GS.Specifications.OriginalLocalCoverageGoal` |
| Pointed neighbourhood model | `GS.NonmanifoldCompletion.original_pointed_neighbourhood_model` | Constructs the local topological comparison used to transfer the cone obstruction |
| No Euclidean chart at the cone vertex | `GS.NonmanifoldTopology.cone_not_euclidean` | `ℝ^e × {Z : Matrix (Fin 2) (Fin d) ℝ | rank Z ≤ 1}`, every `d ≥ 2` |
| Original cone specification | `GS.NonmanifoldTopology.coneProductNonManifold` | Exact type `GS.Specifications.ConeProductNonManifoldGoal` |
| Original GS nonmanifold specification | `GS.NonmanifoldTopology.nonManifold` | Exact type `GS.Specifications.NonManifoldGoal`; `p = 2`, every `q ≥ 3`, `Q₀` orthogonal, `det Q₀ = 1`, all entries of `Q₀` nonzero |
| Older restricted specification | `GS.NonmanifoldTopology.restrictedNonManifold` | Exact type `GS.Specifications.RestrictedNonManifoldGoal`; follows from the all-`q` theorem |
| Older odd-cone specification | `GS.NonmanifoldTopology.oddConeNonManifold` | Exact type `GS.Specifications.OddConeNonManifoldGoal`; follows from the all-width theorem |
| Stronger original-family theorem without the determinant restriction | `GS.Results.gs_not_euclidean_at` | `q ≥ 3`, `Q₀` orthogonal and all its entries nonzero; no assumption on its determinant |
| Explicit singular point in every size `2q` | `GS.Results.reflectionBase_nonEuclidean` | Uses `Q₀ = I − (2/q)J`, where every entry of `J` is one; proves membership and absence of a Euclidean chart |
| Existence of a singular point | `GS.Results.exists_nonEuclidean_point` | Every `q ≥ 3`; the point lies in `localFamily q` |
| Nonvacuity of the original determinant-one assumptions | `GS.Results.exists_specialOrthogonal_nonEuclidean_base` | Every `q ≥ 3`; supplies an orthogonal `Q₀` with determinant one and nonzero entries, together with the nonmanifold conclusion |

Here “nonmanifold” means that the specified point has no open neighbourhood
homeomorphic to an open subset of any finite-dimensional Euclidean space.
The topology is inherited from the original matrix space. This excludes a
topological manifold **without boundary** at that point; no claim about a
manifold-with-boundary structure is implicit in this definition.

The final proof has no user-supplied premise about cone nonmanifoldness,
sphere homology or Brouwer's theorem. The requisite topological results are
proved or imported through proved library theorems. See the
[proof outline](NONMANIFOLD_PROOF.md).
The stronger conclusions and explicit witnesses are in
[`GS/Results/Nonmanifold.lean`](../GS/Results/Nonmanifold.lean).

## Smooth geometry and optimization

| Construction or result | Representative declaration | Scope |
| --- | --- | --- |
| Compact factor groups and quotient homeomorphism onto the matrix orbit | `GS.LieAction.quotientOrbitHomeomorph` | Topological construction for independent block factors |
| Actual smooth manifold structure on the two-factor matrix family | `GS.ManifoldCompletion.inA2Orth_admits_manifold` | Requires `NoOffDiagonalOverlap` |
| Differential of inclusion and the genuine tangent image | `GS.ManifoldCompletion.orbit_tangent_image_iff` | Same no-overlap hypothesis; uses mathlib's manifold differential |
| Orthogonal projection characterized on the genuine tangent fibre | `GS.ManifoldCompletion.pointProjection_unique_tangent_lift` | Same no-overlap hypothesis |
| Positive Frobenius metric on tangent fibres and smooth chart coefficients | `GS.RiemannianCompletion.tangentPairing_pos`, `GS.RiemannianCompletion.chartPairing_smooth` | Original tangent topology is retained |
| Smooth evaluation of the metric on the actual tangent bundle | `GS.GlobalGeometry.tangentMetricExtension_contMDiff`, `GS.GlobalGeometry.tangentMetricExtension_same_base` | No-overlap orbit; smooth ambient pairing on `TM × TM`, restricting to the metric when basepoints agree |
| Globally smooth squared tangent norm | `GS.GlobalGeometry.tangentEnergy_contMDiff`, `GS.GlobalGeometry.tangentEnergy_pos` | Smooth function on the actual tangent bundle, positive for nonzero tangent vectors |
| Intrinsic gradient characterized by the differential | `GS.RiemannianCompletion.intrinsicGradient_characterization` | No-overlap orbit; differentiability assumption on the loss |
| Unique minimizer of the tangent quadratic model | `GS.RiemannianCompletion.tangentQuadraticModel_equality_iff` | Same metric and intrinsic gradient |
| Exponential step with zero tangential acceleration and constant speed | `GS.RiemannianCompletion.stepAcceleration_tangent_lift_zero`, `GS.RiemannianCompletion.stepVelocity_constant_norm` | No-overlap orbit |
| Sufficiently small steps satisfy Armijo descent | `GS.RiemannianCompletion.exponentialStep_armijo` | Differentiable loss and nonzero intrinsic gradient; this is a local step result |
| Procrustes gradient and descent | `GS.RiemannianCompletion.intrinsicGradient_procrustes_eq_neg`, `GS.RiemannianCompletion.procrustes_exponential_armijo` | Quadratic Frobenius loss |
| Cayley curve with the prescribed intrinsic initial velocity | `GS.GlobalGeometry.cayleyTangentStep_contMDiff`, `GS.GlobalGeometry.cayleyTangentStep_mfderiv_one` | No-overlap orbit; a fixed point and tangent vector; smoothness is proved for the time-parametrized curve |
| Smooth Cayley retraction from a fixed tangent fibre | `GS.GlobalGeometry.cayleyFibreRetraction_contMDiff`, `GS.GlobalGeometry.cayleyFibreRetraction_mfderiv_zero` | No-overlap orbit; this fixed-base theorem concerns a fixed fibre. The newer arbitrary-overlap total-bundle theorem is listed below |
| Cayley Armijo descent and termination of geometric backtracking | `GS.GlobalGeometry.cayleyTangentStep_armijo`, `GS.GlobalGeometry.cayley_backtracking_terminates` | Loss differentiable at the starting point; nonzero intrinsic gradient; Armijo constant and backtracking ratio in `(0,1)`, positive initial step |
| Exact projection with sharing and overlap | `GS.GlobalGeometry.exactSharedProjection_minimizes` | Projection onto the explicitly defined generator image; not a general shared quotient-manifold construction |
| Minimum-norm least-squares lift | `GS.Revision.LeastSquares.weightedLift_unique` | Abstract finite-dimensional subspace and linear map; weight conditions occur in the theorem |
| Projected derivative and metric compatibility along curves | `GS.GlobalGeometry.alongDerivative_metric_compatible` | Differentiable matrix fields tangent along the curve; independent factors may overlap |

## Smooth geometry with arbitrary orthogonal overlap

These constructions concern **two independent orthogonal factor layers**, with
arbitrary finite block-label maps and an arbitrary permutation. No no-overlap
hypothesis is imposed. The atlas is constructed on the existing matrix subtype;
its topology is not replaced by a new quotient topology. Names in this table
are in `GS.OverlapGeometry`.

| Result | Declaration | Exact scope |
| --- | --- | --- |
| Actual smooth atlas on the matrix orbit | `overlapChartedSpace`, `overlapIsManifold` | Horizontal complement of the orbit differential; kernel directions integrate to stabilizer elements |
| Original scalar-block family is a manifold | `inA2Orth_admits_manifold` | Exactly `{X : Mat n // InA2Orth c₁ c₂ (permMatrix σ) X}` with its inherited topology |
| Smooth inclusion into matrices | `overlap_val_contMDiff` | The inclusion uses mathlib's actual manifold charts and differential |
| Ambient criterion for smooth maps into the orbit | `overlap_contMDiff_iff_contDiff`, `slice_contMDiff_iff_contDiff` | For maps from a real normed space, manifold smoothness is equivalent to smoothness of the ambient matrix realization; the second theorem applies to the general slice construction |
| Ambient criterion with arbitrary manifold source | `slice_contMDiff_of_ambient`, `slice_contMDiff_iff_ambient` | Applies in particular to the actual tangent bundle; no smooth choice of factor representatives is assumed |
| Injective inclusion differential | `overlap_val_mfderiv_injective` | Every point of the orbit; continuous stabilizers are allowed |
| Full generator image from horizontal directions | `horizontalOrbit_fderiv_zero_range` | Restricting the factor derivative to the horizontal complement preserves the entire `TwoFactorDirection` image |
| Actual manifold tangent image | `orbit_tangent_image_iff` | The image of mathlib's inclusion differential is exactly the original two-factor generator image |
| Unique intrinsic tangent projection | `pointProjection_unique_tangent_lift`, `pointProjection_pythagorean_tangent` | The existing point-only projector lifts uniquely into the actual tangent fibre and minimizes Frobenius distance against every tangent vector |
| Positive Frobenius metric on actual tangent fibres | `tangentPairing_pos`, `tangentMetricCLM` | Pullback through the injective inclusion differential; no change to the chart norm |
| Smooth metric evaluation and energy | `tangentMetricExtension_contMDiff`, `tangentEnergy_contMDiff`, `tangentEnergy_pos` | Actual total tangent bundle for the overlap atlas |
| Intrinsic gradient of the restricted loss | `intrinsicGradient_characterization`, `intrinsicGradient_unique` | Loss differentiable at the base point; the Riesz identity uses the actual manifold derivative |
| Intrinsic stationarity and algorithmic norm | `intrinsicGradient_zero_iff`, `intrinsicGradient_zero_iff_projected`, `intrinsicGradient_norm` | With differentiability, zero intrinsic gradient is equivalent to zero restricted manifold derivative; its metric square is the Frobenius square of the ambient projected gradient |
| Smooth actual tangent-fibre Cayley retraction | `cayleyFibreRetraction_zero`, `cayleyFibreRetraction_contMDiff`, `cayleyFibreRetraction_mfderiv_zero` | Entire tangent fibre at each fixed base point; value at zero is the base point and actual manifold differential there is the identity |
| Smooth retraction on the entire actual tangent bundle | `cayleyRetraction_contMDiff`, `cayleyRetraction_zero_section`, `cayleyRetraction_fibre_mfderiv_zero` | Joint smoothness in the base point and tangent vector on mathlib's actual `TangentBundle`, with its standard smooth structure |
| Prescribed initial velocity and intrinsic Armijo descent | `cayleyTangentStep_mfderiv_one`, `cayleyTangentStep_armijo`, `cayley_backtracking_terminates` | Differentiable loss, nonzero intrinsic gradient, Armijo constant and reduction ratio in (0,1), positive initial step; no convergence-rate assertion |

The [overlap proof guide](OVERLAP_GEOMETRY.md) explains why the local product
inverse-function theorem gives open slice images and why a redundant factor
parametrization creates no smoothness obstruction in this two-factor case.
The no-overlap interfaces listed above remain available with their
original hypotheses. The tangent, gradient, retraction, and descent
theorems above refer to the overlap atlas explicitly.
[RETRACTIONS.md](RETRACTIONS.md) distinguishes the fixed-fibre statements
from the proved arbitrary-overlap total-bundle map.

## Matrix-orbit block geodesics and general dynamics

The block-exponential construction is proved in the actual inherited-topology
matrix orbit. It supplies a smooth all-real curve for every genuine initial
tangent vector. The remaining rows treat general overlap and do not assume an
unproved three-exponential integration lemma.

| Result | Declaration | Exact scope |
| --- | --- | --- |
| Exact scalar-shuffle no-overlap condition | `GS.Geodesics.scalarShuffle_noOverlap`, `scalarShuffleOfSize_noOverlap` | The original permutation is evaluated explicitly; positive block sizes and `b₂ ≤ k₁` suffice, with `n = k₁*b₁` |
| Smooth actual orbit curve and actual tangent velocity | `GS.Geodesics.blockExpCurve_contMDiff`, `blockExpCurve_mfderiv_one` | `L exp(tC) P exp(tΩ) R` takes values in `MatrixOrbit`; its explicit velocity is the inclusion image of the true manifold derivative |
| Blockwise geodesic equation | `GS.Geodesics.scalarShuffle_blockExpCurve_geodesic`, `regularScalarShuffle_blockExpCurve_geodesic` | Actual first and second derivatives and zero induced covariant velocity for all real times; the regular version records `n = k₁*b₁ = k₂*b₂` |
| Every actual initial tangent is realized | `GS.Geodesics.exists_blockExpCurve_of_tangent`, `scalarShuffle_exists_blockExpCurve_of_tangent` | The curve starts at the prescribed matrix point with the prescribed actual manifold velocity; no generator decomposition is assumed |
| Constant blockwise speed | `GS.Geodesics.blockExpCurve_constant_speed` | Squared Frobenius speed is the sum of the squared supported generator norms under no-overlap |
| Exclusive-support commutators are normal | `GS.Geodesics.exclusive_commutator_normal`, `exclusive_commutator_maskedSkew_zero` | Algebraic support and Frobenius-orthogonality identities for the common-coordinate block algebras |
| Balanced generator dynamics have zero residual | `GS.Geodesics.balanced_geodesicResidual_zero` | Exact algebraic certificate for the displayed balanced generators and their proposed derivatives; it does not construct an ODE solution |
| Actual moving-factor differentiation | `GS.OverlapGeometry.moving_product_velocity_hasDerivAt` | Actual derivative hypotheses on factors and time-dependent generators |
| Projected acceleration equals the generator residual | `GS.OverlapGeometry.projected_moving_acceleration`, `projected_moving_acceleration_zero_iff` | At an actual GS point; residual is S' + Π[C,K], with the stated supported skew hypotheses |
| Constant energy under the generator ODE | `GS.OverlapGeometry.geodesicGeneratorEnergy_constant`, `movingProduct_speed_constant` | Actual differentiable generator curves satisfying the residual equation; constant Frobenius energy and moving-product speed |
| Projected derivative on actual tangent fibres | `GS.OverlapGeometry.covariantAlong`, `covariantAlong_pairing` | Ambient derivative projected and lifted to the true tangent space; the pairing is the actual Frobenius pullback metric |
| Symmetric local connection coefficients | `GS.OverlapGeometry.coordinateChristoffel_symmetric` | Projected actual second Frechet derivative of the preferred inverse chart, using symmetry of that derivative |
| Coordinate and along-curve metric compatibility | `GS.OverlapGeometry.coordinateMetric_hasDerivAt`, `covariantAlong_metric_compatible` | Actual coordinate derivatives and tangent-field pairing identities; no global bundled connection registration |

[ORTHOGONAL_GEODESICS.md](ORTHOGONAL_GEODESICS.md) gives the complete written
proof of the three-exponential formula for every initial tangent vector,
for independent orthogonal and unitary layers with arbitrary overlap. The full integration
and global geodesic flow are **not yet Lean-certified**. This boundary is
separate from the proved formal statements in the table.
[BLOCK_GEODESICS.md](BLOCK_GEODESICS.md) gives the complete no-overlap matrix
proof and explains the remaining global connection-registration boundary.

## Arbitrary overlap and physical sharing

The descent and sharing results below use finite-dimensional projections and
actual factor curves. They do not require `NoOffDiagonalOverlap` or assume a
shared quotient atlas. The independent-factor overlap atlas is established
separately above.
All names in this table are in `GS.GlobalGeometry`.

| Result | Declaration | Exact scope |
| --- | --- | --- |
| Gradient on the factor-differential image | `projectedGradient_represents`, `projectedGradient_eq_zero_iff` | Independent supported orthogonal factors and an arbitrary permutation; overlap is allowed |
| Feasible Cayley backtracking in the original family | `inA2Orth_cayley_backtracking` | Actual `InA2Orth`; differentiable loss, nonzero projected gradient, positive initial step, Armijo constant and reduction ratio in `(0,1)` |
| Constrained local minima are stationary | `inA2Orth_localMin_stationary` | Local minimum on the original `InA2Orth` family and differentiability at the point |
| Physical block ties survive exponentiation | `expLine_tied` | Equal full physical blocks; positive block size dividing the ambient matrix size |
| Exact constrained adjoint | `shared_factor_derivative_adjoint` | Adjoint of the factor derivative using the Frobenius metric on expanded physical generators |
| Coupled normal equations | `shared_normal_equation_iff_coupled`, `shared_normal_equation_iff_projection`, `shared_normal_equation_iff_minimizes` | Concrete tied skew-generator spaces; overlap cross terms retained; no normal-solvability assumption |
| Existence of a normal-equation solution | `exists_shared_normal_solution` | The synthesized matrix is the unique image projection; generators may have a nontrivial kernel |
| Generator image equals actual factor velocities | `sharedFactorVelocity_iff_direction` | Fixed shared orthogonal base factors, arbitrary within-factor tie maps, positive block sizes dividing the matrix size |
| Projection over actual feasible velocities | `exactSharedProjection_is_factor_velocity`, `exactSharedProjection_minimizes_factor_velocity` | Same full-block hypotheses and an orthogonal carrier; exponential curves realize the projected velocity |
| Feasible shared Armijo backtracking | `exists_feasible_shared_armijo_step` | Same full-block hypotheses and actual shared orthogonal base factors; differentiable loss, nonzero shared projected gradient, and standard Armijo/backtracking parameter ranges |
| Shared local-minimum stationarity | `shared_localMin_stationary` | Differentiable loss and a local minimum along the specified shared negative-gradient curve; stationarity is relative to the fixed factor presentation |

For a differentiable loss, vanishing projected gradient is first-order
stationarity on the specified directions. A bare identity involving `fderiv`
without differentiability uses mathlib's totalized derivative convention and
must not be interpreted as a stationarity theorem for a nonsmooth loss.

Factor-curve realization and image-curve lifting are distinct results.
The shared geometry below establishes presentation independence, a compact
factor-group action, an atlas on its actual orbit, and local image-curve lifts.

### Shared geometry

All names below are in `GS.SharedGeometry`. `Pattern` contains only arithmetic block-layout
hypotheses and the within-layer label map, not geometric assumptions.

| Statement | Declaration | Scope |
| --- | --- | --- |
| Invertible tied matrices retain their ties under inversion | `sharedMatrixSpace_inverse` | A finite-dimensional unital supported tied algebra; positive complete block sizes |
| Cayley closure in both directions | `cayley_shared`, `cayley_sharedSkew` | Every shared skew generator is admissible; inverse coordinates require the usual Cayley source |
| Actual compact shared factor group and smooth group operations | `Pattern.subgroup`, `factorCompactSpace`, `factorIsManifold`, `factorLieGroup` | Inherited matrix topology, explicit Cayley transitions, genuine mathlib LieGroup class |
| Exact shared family and compact homogeneous quotient | `orbit_iff_inShared`, `quotientOrbitHomeomorph` | Actual `InSharedA2Orth`; arbitrary carrier matrix; topological, not a presumed smooth quotient |
| Open orbit map | `orbitMapToOrbit_isOpenMap` | Does not assert a continuous or smooth local factor section |
| Point-only direction range and presentation independence | `sharedDirection_iff_pointDirections`, `sharedDirection_factor_independent` | Full within-layer block sharing, including overlap; no factor-lifting premise |
| Constant range dimension along an orbit | `directionActionEquiv`, `finrank_pointDirections_constant` | Explicit linear transport by the actual group action |
| True coordinate differential | `orbitParam_fderiv_zero`, `orbitParam_fderiv_zero_range` | Differentiated actual Cayley formula, with coefficients -2 and +2; range equals point-based directions |
| Exact nonlinear stabilizer in Cayley coordinates | `factorLift_stabilizes_iff_kernel` | Both directions, on the entire shared Cayley parameter domain |
| Canonical projector equals existing coupled projection | `exactSharedProjection_eq_pointProjection`, `exactSharedProjection_factor_independent` | Orthogonal carrier; arbitrary valid presentations of the same matrix |
| Equivariant projector and joint continuity | `pointProjection_equivariant`, `continuous_pointProjection` | Continuity on the actual fixed orbit times ambient matrices, not across rank-changing off-orbit points |
| Projected velocity realized at every base factor pair | `pointProjection_is_factor_velocity` | Actual differentiable tied-factor curves |

The smooth construction uses explicit local product charts and horizontal
slices. Its principal results are:

| Statement | Declaration | Scope |
| --- | --- | --- |
| Horizontal/stabilizer local product | `sliceProduct_hasFDerivAt_zero`, `sliceProductChart` | Actual multiplication in shared Cayley coordinates; derivative is the complement/kernel equivalence |
| Open horizontal image in the full orbit | `horizontalChartImage_open` | Follows from the open orbit map and local product chart, not a selected image branch |
| Genuine inherited-topology manifold | `sharedOrbitChartedSpace`, `sharedOrbitIsManifold`, `inSharedA2Orth_admits_manifold` | Complete physical blocks within each layer, any fixed real carrier `P`, including continuous stabilizers |
| Smooth injective inclusion differential | `sharedOrbit_val_contMDiff`, `sharedOrbit_val_mfderiv_injective` | Actual mathlib `mfderiv` for the constructed atlas |
| Complete tangent-image identification | `orbit_tangent_image_iff`, `tangent_image_iff_sharedDirection` | Both directions, at every orbit point and for every valid factor presentation |
| Exact coupled projection has a unique actual tangent lift | `exactSharedProjection_unique_tangent_lift` | Orthogonal carrier only for comparison with the older factor-based projector |
| Positive smooth Frobenius metric | `tangentPairing_pos`, `tangentMetric_compatible_data`, `tangentMetricExtension_contMDiff` | Actual tangent fibres, their topology and smooth evaluation on the total bundle |
| Local smooth factor section | `exists_local_smooth_factor_section` | Right inverse on an open neighbourhood of every matrix point; valid shared factors at all inputs |
| Local lifts of image curves | `exists_local_smooth_factor_curve`, `exists_local_differentiable_factor_curve` | Smooth or differentiable at the given parameter; reconstruction on a neighbourhood, no global section |
| Joint smoothness of the canonical projector | `pointProjection_contMDiff` | Whole fixed orbit times ambient matrices; arbitrary carrier `P` |
| Intrinsic gradient and true restricted-loss derivative | `intrinsicGradient_characterization`, `intrinsicGradient_unique`, `intrinsicGradient_zero_iff` | Differentiability of the loss at the base point where required |
| Smooth matrix realization of the intrinsic gradient | `intrinsicGradient_ambient_contMDiff` | Top-order ambient loss; the full bundle statement and weaker regularity are supplied below |

The optimization results allow any fixed real carrier matrix, including
singular and zero matrices. The generator metric uses expanded physical matrices and hence
includes every block's actual multiplicity.

| Statement | Declaration | Scope |
| --- | --- | --- |
| Canonical physical minimum-norm lift | `minimumNormLift_synthesis`, `minimumNormLift_horizontal`, `minimumNormLift_unique` | Every matrix point and ambient input; image projection constructed, not assumed |
| Exact reconstruction, excess norm and unique minimizer | `minimumNormLift_reconstruct`, `minimumNormLift_pythagorean`, `minimumNormLift_unique_minimizer` | Full coupled synthesis kernel, not overlap-only coordinates |
| Equivariance and representative formula | `minimumNormLift_equivariant`, `minimumNormLift_factor_formula` | Conjugation by actual shared orthogonal factors |
| Smooth canonical generator recovery | `minimumNormLift_contMDiff`, `tangentGenerators_contMDiff` | Whole fixed orbit times ambient matrices, then the actual total tangent bundle |
| All-time feasible point-only Cayley step | `sharedCayleyValue_mem_orbit`, `sharedCayleyValue_derivative` | Every real time; derivative is the exact projected input |
| Whole-bundle canonical retraction | `cayleyRetraction_contMDiff`, `cayleyRetraction_zero_section`, `cayleyRetraction_fibre_mfderiv_zero` | Genuine TangentBundle and mfderiv; identity on every zero fibre |
| Intrinsic canonical descent | `negative_gradient_loss_derivative`, `cayleyTangentStep_armijo`, `cayleyRetraction_backtracking_terminates` | Differentiable loss at the base, nonzero gradient and standard parameter ranges |
| Smooth true tangent projector | `tangentProjectionBundle_contMDiff` | Map into the actual tangent bundle, not only its ambient matrix realization |
| Full gradient-section regularity | `intrinsicGradientSection_contMDiff_of_order`, `intrinsicGradientSection_smooth` | C^(r+1) loss gives C^r section; genuine C-infinity case included |
| Exact update regularity | `gradientUpdate_contMDiff_of_order`, `gradientUpdate_smooth` | Jointly in point and real step size; no smoothness claim for a discrete backtracking selector |

The separate unitary extension is indexed below. General equalities between individual entries, partial blocks,
and constraints between different layers remain outside these full-block
orthogonal subgroup theorems. No executable pseudoinverse solver, floating-point
Cayley implementation, convergence rate or general shared geodesic theorem is
asserted.

### Canonical unitary descent

In `GS.UnitaryManifold.CanonicalDescent`, `loss_along_canonicalCayleyStep` and
`canonical_negative_gradient_loss_derivative` use the existing actual velocity
of the canonical retraction. `canonicalCayleyStep_armijo` gives eventual strict
Armijo decrease. `cayleyRetraction_backtracking_terminates` states finite
geometric backtracking directly using the whole-bundle `cayleyRetraction`.
Chosen-chart descent is a separate interface. There is no optimizer
convergence rate or floating-point implementation claim.

## Complex unitary algebra and projections

All names in this table are in `GS.UnitaryGeometry`. Complex matrices are viewed
as a real inner-product space with pairing `Re trace(Aᴴ B)`.

| Result | Declaration | Exact scope |
| --- | --- | --- |
| Structured unitary QR/RQ | `structuredQR`, `structuredRQ` | Arbitrary block-label support and permutation; input determinant is a unit; unitary supported factor and upper-triangular remainder are constructed |
| Two-factor unitarization | `twoFactorUnitarization` | `(CInA2 ... A ∧ Unitary A) ↔ CInA2Unitary ... A`; arbitrary natural block sizes and permutation |
| Three-factor unitarization | `threeFactorUnitarization` | Corresponding exact `CInA3` equivalence with two arbitrary permutations; no divisibility condition or assumed QR theorem |
| Skew-Hermitian supported projection | `maskedSkewHermitian_pythagorean`, `maskedSkewHermitian_unique_minimizer` | Symmetric entry mask; exact unique Frobenius projection, including imaginary diagonal entries |
| Trace-free supported projection | `maskedTracelessSkewHermitian_minimizes`, `maskedTracelessSkewHermitian_unique_minimizer` | Symmetric mask containing every diagonal; competitors are supported, skew-Hermitian, and have total trace zero |
| Generator metric and kernel | `tangentParam_frobSq_cross`, `tangentParam_eq_zero_iff` | Unitary boundary factors and carrier; retains the overlap cross term and characterizes zero image by `Ω = −Pᴴ C P` |
| Smooth real projection maps | `maskedSkewHermitian_contDiff`, `maskedTracelessSkewHermitian_contDiff` | Real continuous-linear formulas are smooth in the ambient matrix topology; projection membership/minimality retain the mask hypotheses above |
| Unavoidable phase ambiguity | `tangentCoreMap_not_injective`, `tangentParamMap_not_injective` | Every positive matrix dimension and arbitrary block labels with unitary carrier; the nonzero pair `(iI, −iI)` maps to zero |
| Canonical polynomial generators | `balancedLeft`, `balancedRight`, `balanced_reconstruct_tangent` | Supported skew-Hermitian generators depending only on the matrix point and tangent vector; arbitrary independent overlap |
| Polynomial formula for the actual projector | `polynomialPointProjection_eq`, `polynomialPointProjection_smooth` | Equality with the established real-Frobenius projector on the GS orbit; the ambient polynomial extension is jointly smooth |

The trace-free result imposes total trace zero; it does not impose zero trace
separately on every physical block. These are support, factorization, projection,
and generator-metric results. The independent two-factor orbit atlas is now
proved separately below; an arbitrary shared unitary tangent bundle remains
a separate task.
The proved phase-kernel result exhibits the obstruction to copying the real
discrete-stabilizer atlas argument: opposite imaginary scalar generators cancel
even without off-diagonal overlap. It does not obstruct manifoldness of the
compact orbit or uniqueness of projection onto the matrix image.

## Smooth unitary two-factor geometry

All names in this table are in `GS.UnitaryManifold`. The ambient complex
matrix spaces and the model spaces are treated as real normed spaces. The
topology on the orbit is inherited from matrices. These are statements for
two independent supported factor layers, allowing arbitrary overlap.

| Result | Declaration | Exact scope |
| --- | --- | --- |
| Smooth supported unitary block group | `blockUIsManifold` | Cayley atlas on the original block-unitary subgroup, with supported skew-Hermitian model space |
| Full-unitary real model dimension | `finrank_fullModel` | The complete skew-Hermitian model has real dimension `q²`, including diagonal phase directions |
| Smooth atlas on the matrix orbit | `overlapIsManifold` | Horizontal coordinates remove the full derivative kernel, including the diagonal phase directions |
| Original scalar-block family is a manifold | `inA2Unitary_admits_manifold` | Exactly `{X : CMat n // CInA2Unitary c₁ c₂ (cPermMatrix σ) X}` with inherited topology |
| Smooth inclusion into complex matrices | `overlap_val_contMDiff` | Smoothness over the real field using the constructed charts |
| Injective actual inclusion differential | `overlap_val_mfderiv_injective` | The differential on the manifold tangent fibre is injective, despite noninjectivity of the redundant factor coordinates |
| Exact actual tangent image | `orbit_tangent_image_iff` | The image of the inclusion differential equals the two-factor supported skew-Hermitian generator image |
| Unique intrinsic projection and its least-squares identity | `pointProjection_unique_tangent_lift`, `pointProjection_pythagorean_tangent` | The canonical point-only projector lifts uniquely to the actual tangent fibre; phase redundancy creates no ambiguity in the resulting vector |
| Joint smoothness of the actual projector | `pointProjection_joint_contMDiff` | Smooth in both the actual orbit point and ambient matrix direction, without chosen smooth factors |
| Positive Frobenius metric with the actual tangent topology | `tangentPairing_pos`, `tangentMetric_compatible_data` | Pullback of Re trace(Aᴴ B), retaining the original chart norm |
| Smooth total-bundle metric evaluation and energy | `tangentMetricExtension_contMDiff`, `tangentEnergy_contMDiff`, `tangentEnergy_pos` | Actual unitary tangent bundle as a real smooth manifold |
| Pointwise intrinsic gradient | `intrinsicGradient_characterization`, `intrinsicGradient_unique`, `intrinsicGradient_zero_iff` | Differentiable ambient loss; actual restricted manifold derivative, Riesz identity, uniqueness, and stationarity |
| Smooth fixed-base Cayley retraction | `fibreRetraction_zero`, `fibreRetraction_contMDiff`, `fibreRetraction_mfderiv_zero` | Defined on the whole tangent fibre at each fixed point, with identity actual manifold differential at zero |
| Actual initial velocity of the retraction curve | `fibreRetraction_curve_velocity` | Ambient derivative of t ↦ R_X(tv) is the included actual tangent vector at zero |
| Canonical smooth retraction on the whole tangent bundle | `cayleyRetraction_contMDiff`, `cayleyRetraction_zero_section`, `cayleyRetraction_fibre_mfderiv_zero` | Actual `TangentBundle` domain; a point-only formula, zero section fixed, identity actual fibre differential; arbitrary overlap |
| Intrinsic fixed-base Armijo descent and finite backtracking | `fibre_negative_gradient_loss_derivative`, `fibreRetractionStep_armijo`, `fibre_backtracking_terminates` | Ambient loss differentiable at X, nonzero intrinsic gradient, Armijo constant and shrink ratio in (0,1), positive initial step; no uniform bound or convergence theorem |

The [unitary manifold guide](UNITARY_MANIFOLD.md) explains the constructed
factor charts, stabilizer integration, and open slice images. The
[unitary optimization guide](UNITARY_OPTIMIZATION.md) explains how the ambient
Frobenius formulas connect to the actual metric and gradient. These gradient
theorems are pointwise; a smooth varying-base gradient section is not yet
packaged. Joint projector smoothness and the canonical whole-bundle retraction
are proved separately. The chosen-factor fibre retraction and its descent
theorems remain valid and are not silently identified with the canonical map.

## Unitary counterexamples

| Statement | Declaration | Exact scope |
| --- | --- | --- |
| Four-factor unitary insufficiency | `GS.UnitaryFour.counterexample` | Exact `6 × 6` matrix; four factors with `2 × 2` diagonal blocks and the prescribed perfect shuffle at each connector; all complex unitary factorizations are excluded |
| Strict inclusion | `GS.UnitaryFour.strictInclusion` | `CInA4Unitary` is a proper subset of `CInA4 ∩ U(6)` for the same family |
| Universal complex determinant-modulus obstruction | `GS.UnitaryFour.necessaryCondition` | Applies to arbitrary complex unitary factors, with the displayed nonzero-denominator hypothesis |
| Nonadditive actual curve velocities | `GS.UnitaryNonmanifold.witnessVelocity_sum_not_feasible` | Original scalar-shuffle `CInA3Unitary 2 3 2 P Pᴴ` family at the rational point `Q₀ ⊗ I₂`; two individually feasible velocities have a nonfeasible sum |
| No differentiable local ambient retraction | `GS.UnitaryNonmanifold.unitary_three_no_differentiable_local_retraction` | Excludes every local retraction differentiable at this point |
| No embedded differentiable flattening chart | `GS.UnitaryNonmanifold.unitary_three_no_local_differentiable_flattening` | Arbitrary normed real tangent and normal coordinate spaces; in particular, no embedded `C1` submanifold chart |

The complex four-factor exclusion is proved directly using moduli of block
determinants; it is not inferred solely from real nonmembership. The
three-factor smoothness obstruction concerns **every** differentiable feasible
matrix curve, whether or not its factors have differentiable lifts.
It is an embedded smoothness counterexample at `q = 3`, not a theorem excluding
an arbitrary abstract topological manifold structure. See
[UNITARY_COUNTEREXAMPLES.md](UNITARY_COUNTEREXAMPLES.md). The stronger written
local-model argument below is a separate result with a different verification
status.

## Unitary neighbourhood model and topological nonmanifoldness

`GS.UnitaryTopology.unitary_matrix_pointed_neighbourhood_model` proves an
actual pointed neighbourhood model for the **complete original matrix
family**, with its inherited topology, at `scalarBlockBase Q`. Its exact
target is

```
OuterFactors q o × ((Fin ((q−1)²) → R) × {W : R^(3×(q−1)²) | rank W ≤ 1}).
```

The assumptions are that `Q` is unitary and its anchor row and column at `o`
are nonzero. There is no supplied local-model or selected-branch coverage
premise. The local model is not restricted to odd q; that restriction occurs
in the following formal nonmanifold theorem.

[UNITARY_LOCAL_STRUCTURE.md](UNITARY_LOCAL_STRUCTURE.md) gives a complete
mathematical proof that, for the `(2,q,2)` family and `q >= 2`, a neighbourhood
of `Q ⊗ I₂` has the form

```
R^(q^2 + 6q - 3) x { W in R^(3 x (q-1)^2) : rank W <= 1 }.
```

The first row and column of Q must be nonzero. Polar normalization removes
independent outer unitary factors; row/column phase normalization leaves a
smooth central slice of dimension `(q-1)^2`. The remaining common traceless
Hermitian direction is a two-sphere. The written proof checks exact fibres
and full-neighbourhood coverage, then derives topological nonmanifoldness
for every `q > 2` from torsion local homology. An explicit admissible Q is
provided for every such q.

The numerical Euclidean-factor replacement `R^(q²+6q−3)` in that written
formula is not yet a separately packaged formal theorem. The actual outer
group is proved locally Euclidean, which suffices for the formal odd-q
topological transfer. The following results are proved:

| Component | Declaration | Exact boundary |
| --- | --- | --- |
| Dephased chart of the full unitary slice | `GS.UnitaryLocalModel.dephased_chart_exists`, `dephasedChartHomeomorph` | Open inherited-topology slice neighbourhood and open kernel coordinates, constructed by the implicit-function theorem |
| Dimension of the dephased coordinates | `GS.UnitaryLocalModel.finrank_dephasedModel` | Real dimension `(q−1)²`; constraint surjectivity is proved by explicit phase generators |
| Exact normalization algebra and polar uniqueness | `GS.UnitaryLocalModel.phase_normalization_block`, `positive_polar_unique` | Common unitary basis, fixed right anchor, and uniqueness of positive polar factors |
| Compact middle-image homeomorphism | `GS.UnitaryLocalModel.exists_compact_middle_homeomorphism_to_cone` | Exact zero and nonzero fibres, including the collapsed sphere |
| Full compact matrix-image homeomorphism | `GS.UnitaryLocalModel.exists_full_compact_homeomorphism` | Retains every outer factor; positive anchor uniqueness recovers all outer coordinates |
| Coverage of every nearby original-family matrix | `GS.UnitaryLocalModel.exists_open_full_compact_coverage` | Compact full-factor space and an open set containing the entire base fibre; no chosen branch or continuous factor selection |
| Actual full-family neighbourhood model | `GS.UnitaryTopology.unitary_matrix_pointed_neighbourhood_model` | Unitary Q with nonzero anchor row and column; target is exactly `OuterFactors × ConeCoordinates ((q−1)²)` in inherited topologies |
| Unconditional three-row cone obstruction for selected widths | `GS.UnitaryTopology.rankThreeProduct_not_euclidean_of_four_dvd`, `odd_q_model_not_euclidean` | Any Euclidean factor and positive cone width divisible by four; in particular `(q−1)²` for odd `q ≥ 3`; no GS neighbourhood premise |
| Topological nonmanifoldness of the full unitary GS family | `GS.UnitaryTopology.unitary_gs_not_euclidean_at` | Every odd `q ≥ 3`; original scalar `(2,q,2)` family; arbitrary unitary Q with nonzero anchor row and column |
| Explicit singular points and nonvacuity | `GS.UnitaryTopology.unitaryReflection_nonEuclidean`, `exists_unitary_nonEuclidean_point` | Every odd `q ≥ 3`; exact complex embedding of the Householder base and original-family membership |

The bridge recovers the outer gauges, proves uniform full-family coverage,
and uses the established passage from neighbourhood images to open germs.
The resulting odd-q theorem is a genuine topological conclusion about the
matrix family, stronger than the `q = 3` embedded smoothness
obstruction. Even-q model widths still require another formal topological
obstruction; the all-q torsion-homology calculation is not Lean-certified.
[UNITARY_EVEN_TOPOLOGY.md](UNITARY_EVEN_TOPOLOGY.md) records the remaining
ordinary mathematical route without claiming a formal even-q theorem.

## Shared geodesics and unitary sharing

These results are included in the supported library.
[SHARED_GEODESICS.md](SHARED_GEODESICS.md) and
[UNITARY_OPTIMIZATION.md](UNITARY_OPTIMIZATION.md) describe their constructions
and exact scope.

| Topic | Exact namespace/declarations | Boundary |
| --- | --- | --- |
| Shared induced connection | `GS.SharedGeometry.covariantAlong`, `covariantAlong_metric_compatible` | Actual tangent projection of the ambient derivative; not an abstract global connection registration |
| Orthogonal shared geodesics | `GS.SharedGeodesics.orthogonalExpCurve_covariantVelocity_zero`, `exists_orthogonalExpCurve_of_tangent` | Actual shared matrix orbit, every genuine initial tangent, all real times, no off-diagonal overlap |
| Physical speed and factor independence | `orthogonalExpCurve_constant_speed`, `orthogonalExpCurve_factor_independent` in `GS.SharedGeodesics` | Physical block multiplicities retained; equality from actual point/velocity data |
| Exact shuffle specialization | `GS.SharedGeodesics.scalarShuffle_shared_geodesic`, `scalarShuffle_shared_exists_geodesic` | `left.size <= k1` for the precise scalar shuffle, not arbitrary permutations |
| Unitary shared geometry | `GS.UnitarySharing.sharedOrbitIsManifold`, `inSharedA2Unitary_admits_manifold`, `orbit_tangent_image_iff` | Full repeated physical blocks; arbitrary fixed complex carrier; real geometry |
| Unitary shared optimization | `GS.UnitarySharing.cayleyRetraction_contMDiff`, `intrinsicGradientSection_smooth`, `cayleyRetraction_backtracking_terminates` | True total tangent bundle; canonical physical lift; no executable-solver guarantee |
| Full complex normal equations | `GS.UnitarySharing.pointNormalEquation_iff_minimizes` | All tied entries, not an overlap-only residual |
| Mandatory phase kernel | `GS.UnitarySharing.pointMap_not_injective` | Any positive ambient dimension and every carrier |

## Statements not established by this project

- `GS.Revision.Specifications.GeneralRankOneNonManifoldGoal` quantifies over
  **all** row and column sizes at least two. The proved two-row cone theorem
  does not by itself inhabit this more general specification.
- `SphereHomologyProfile` remains an explicit unconstructed input to the conditional
  homology route. It is not an axiom and is not needed by the final topological
  proof. Homotopy invariance of singular homology and the low-dimensional
  computations are separate proved results.
- An algebraic shared projector alone does not supply a manifold.
  The library constructs the full-block orthogonal orbit atlas and actual
  tangent bridge separately. Complete-block unitary sharing has its own
  corresponding construction. Partial-block and cross-layer equality constraints
  remain outside both field constructions.
- Smooth metric evaluation and squared tangent norm are proved on the
  actual tangent bundle. Registration as a `Bundle.RiemannianMetric` object
  in a different library API and construction of an intrinsic path distance
  remain outside the statements here.
- The projected derivative, symmetric local Christoffel coefficients, and
  metric compatibility are proved. A global bundled Levi-Civita connection
  and the full formal three-exponential integration remain separate.
- The canonical unitary total-bundle retraction and joint projector smoothness
  are proved. The shared-unitary namespace supplies a smooth bundled gradient for
  sufficiently regular losses. A compatibility theorem transporting this result
  to the separate independent atlas is not implicitly asserted.
- Local descent does not imply convergence rates, global convergence or a
  numerical complexity bound for an optimizer. No spectral-norm Muon update
  theorem is asserted here.

The [paper correspondence](PAPER_COVERAGE.md) distinguishes article claims
from additional results. [REMAINING_WORK.md](REMAINING_WORK.md) describes
unformalized interfaces and mathematical extensions.

## Special-unitary sharing: experimental, uncompiled sources

The SU source is an unfinished experimental development under
`experimental/special_unitary`, excluded from the supported build. All names below have prefix
`GS.SpecialUnitarySharing` unless explicitly qualified.

| Interface | Exact source scope |
| --- | --- |
| `BlockTraceZero`, `BlockDetOne` | Literal per-physical-block conditions, not total trace/determinant |
| `Orbit.quotientOrbitHomeomorph` | Genuine SU quotient with the original matrix topology |
| `specialFactorIsManifold`, `specialFactorLieGroup` | Separate SU factor atlas from local exponential coordinates |
| `inSharedA2SU_admits_manifold` | Actual smaller SU family with its own horizontal atlas |
| `orbit_tangent_image_iff` | Full range of the actual inclusion differential |
| `exists_local_smooth_factor_section` | Genuine local SU factor section without global selection |
| `pointNormalEquation_iff_minimizes` | Full least squares with all physical ties and trace constraints |
| `minimumNormLift_unique_minimizer` | Physical Frobenius weights, including multiplicities |
| `pointProjection_contMDiff`, `minimumNormLift_contMDiff` | Joint smoothness on the true SU orbit |
| `toUnitaryOrbit_contMDiff` | Smooth inclusion; does not identify SU and U tangent spaces |
| `tangentMetricExtension_contMDiff` | Positive smooth induced metric on the actual tangent bundle |
| `orbitExpStep_contMDiff` | Smooth, exactly SU-valued finite update |
| `expRetraction_contMDiff`, `expRetraction_fibre_mfderiv_zero` | Entire actual tangent-bundle domain and identity fibre differential |
| `intrinsicGradientSection_contMDiff_of_order` | Actual gradient section with C^(r+1)-to-C^r regularity |
| `expRetraction_backtracking_terminates` | Intrinsic backtracking with that same retraction |
| `factorLift_stabilizes_of_kernel` | Kernel exponentiation used for the slice, not a false global inverse |
| `Regression.cayley_does_not_preserve_SU3` | Ordinary Cayley cannot simply be restricted to SU generators |
| `Regression.exists_nonzero_SU_synthesis_kernel` | Trace-free stabilizers can remain |

[SPECIAL_UNITARY_SHARING.md](SPECIAL_UNITARY_SHARING.md) explains the local IFT
and trace argument. The first remaining task is compiling these proofs together
with their dependencies. This experimental development does not establish
SU geodesics, executable solver correctness, floating-point error bounds,
or global optimizer convergence.

