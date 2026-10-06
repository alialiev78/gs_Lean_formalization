# Paper correspondence

Source: Ali Aliev and Maxim Rakhuba, *Riemannian Structure and Optimization for
a Class of Low-Parametric Orthogonal Matrices*, arXiv:2609.27982 (2026).

The table maps the paper's topics and named statements to the library.
Exact Lean declarations determine the hypotheses and scope of each result.
See [VERIFICATION.md](VERIFICATION.md) for reproducible build instructions.

| Source location or label | Lean correspondence | Qualification |
| --- | --- | --- |
| Definition `GS_main_definition` | `GS.RectBlockDiagonal`, `GS.InWord`, `GS.InA2`, `GS.InA3`, `GS.InA4` | Selected square-word interfaces; no general dependent rectangular chain |
| Proposition `prop:gs_expansion` | `GS.Revision.Cells.product_block`, `GS.Results.OriginalCellRank.inA2_iff_block_rank` | Exact expansion and a stronger if-and-only-if rank criterion |
| Section 2.1, rectangular/square bounded-rank examples | Cell algebra and explicit rank-one-cone results | Not a complete topological classification of all determinantal products |
| Section 2.2, smooth two-factor O/U images | `GS.OverlapGeometry.inA2Orth_admits_manifold`, unitary orbit atlas | Actual inherited topology, smooth inclusion and tangent-image identification; no black-box custom orbit axiom |
| `similarity_PS`, `corollary:similarity_PS` | `GS.shuffle_kron`, `GS.shuffle_block_entry` | Explicit finite-index identities |
| Tangent projection and `lemma:overlap_indices` | `GS.Projection`, `GS.OverlapGeometry`, `GS.LieAction.perfectShuffle_noOverlap` | Arbitrary overlap handled; coordinate masks must be transported under permutation |
| AD section `subsec:ad_implementation` | `hasDerivAt_loss_tangent_line`, `fderiv_product2_generators`, adjoint pairing identities | Mathematical chain rule only; no AD implementation verification |
| Sharing section `subsec:sharing` | `GS.SharedGeometry`, `GS.UnitarySharing`, shared normal equations | Complete within-layer physical blocks; not arbitrary entry ties |
| Retraction section `subsec:retraction` | Whole-bundle Cayley constructions, intrinsic descent and backtracking | Canonical functions and identity fibre differentials; no floating-point guarantee |
| `prop:time_complexity`, `prop:space_complexity` | Some arithmetic/storage identities | Algorithmic time and memory bounds are not formalized |
| Boundary permutations, vector transport, `lemma:block_diag_proj` | Boundary Frobenius invariance, block projection multiplication and projected derivative identities | No GPU cost theorem or complete global connection registration |
| Experiments | Arithmetic checks of supplied table entries only | Training, datasets, statistical conclusions and performance are not verified |
| Appendix A, `cor:modified-QR`, `prop:m3` | `GS.Results.Algebra.structuredQR`, `structuredRQ`, `threeFactorOrthogonalization`, `threeFactorUnequalBlocks` | Constructed QR/RQ; paper's diagonal-commutator proof is not reproduced line by line |
| Appendix A, `(p,2,p)` CS reduction | `GS.CS.exists_square_cs_angles`, `inA3Orth_scalar_two_iff` | Complete decomposition, including degenerate singular values |
| Appendix A, local-model construction | Original same fibres, normalization, compact quotient and full-family neighbourhood coverage | Covers an entire sufficiently small neighbourhood, not only a parametrized branch |
| `lem:C2d_not_manifold_odd` and concluding argument | `GS.NonmanifoldTopology.coneProductNonManifold`, `GS.Results.gs_not_euclidean_at` | Stronger: all cone widths `d >= 3` and real `q >= 3`; an alternative topological proof is used |
| Appendix B, nonoverlap geodesics | `GS.Geodesics.scalarShuffle_blockExpCurve_geodesic`, `GS.SharedGeodesics` | Actual orbit, every initial tangent, constant speed and all real times under nonoverlap |
| Appendix B, cited covering/Hopf--Rinow, lengths and curvature | Concrete metric/differential identities | General background theorems and their full library interfaces are not formalized here |
| Hierarchical/higher-order appendix | Four-factor obstruction, explicit counterexample and open exclusion | No full hierarchical flattening/depth theorem |
| Invertible-block appendix | Selected examples and algebraic obstructions | No complete classification or formal noncompact-orbit optimization theory |
| Compact-group appendix | Detailed real geometry of unitary blocks and sharing | The paper mentions U and SO; the complete U implementation details and separate SU development are additional formal work |

## Additional results

Beyond the source's explicit arguments, the library supplies complex two- and
three-factor unitarization, complete complex CS decomposition, a genuine
four-unitary-factor obstruction, full unitary local-neighbourhood models and
odd-q topological singularities, minimum-physical-norm lifts, and actual smooth
gradient sections with finite differentiability regularity. These are extensions
or expanded formal details; no independent novelty claim is made.

## Fidelity boundaries

The mathematical domain is exact real or complex arithmetic. The geometry is
real geometry even for unitary matrices. Numerical software, asymptotic program
cost, optimization convergence, even-q unitary topology and general unitary
geodesics are outside the certified claims. Every conditional reduction retains
its hypotheses in Lean; source presence alone is not called a kernel proof.
