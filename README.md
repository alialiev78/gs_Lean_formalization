# Structured orthogonal and unitary matrices in Lean 4

Developed with assistance from OpenAI's ChatGPT. We are confident in the results of the paper, but we cannot independently verify the formalization. There may be errors, and the research community is invited to find and correct them.

This repository formalizes mathematical results from:

> Ali Aliev and Maxim Rakhuba, **Riemannian Structure and Optimization for a Class of Low-Parametric Orthogonal Matrices**, arXiv:2609.27982 (2026).

[Paper](https://arxiv.org/abs/2609.27982) ·
[Paper correspondence](docs/PAPER_COVERAGE.md) ·
[Theorem index](docs/RESULTS.md) ·
[Source map](docs/ARCHITECTURE.md) ·
[Remaining work](docs/REMAINING_WORK.md) ·
[Publishing guide](docs/PUBLISHING.md)

The Lean proofs may differ from the paper's presentation. The library also
contains some extensions.

The supported library contains 370 O/U modules. The 36 experimental SU modules
are unfinished and excluded from the supported build. Precise theorem types
and the [coverage map](docs/PAPER_COVERAGE.md) specify the mathematical scope.

## Mathematical objects and conventions

A structured matrix is a product of square block-diagonal matrices interleaved
with fixed coordinate permutations. In the two-factor case,

$$
X=B_2 P B_1.
$$

The central questions are when orthogonality of the product can be realized by
orthogonal factors, when the image is a smooth manifold in its **inherited matrix
topology**, and how to construct intrinsic optimization maps on that image.

- Orthogonal matrices are real matrices satisfying the two Gram identities.
- Unitary matrices are complex matrices satisfying the conjugate-transpose
  Gram identities. Their manifold and optimization theory is **real** geometry,
  with the real Frobenius metric $\operatorname{Re}\operatorname{tr}(A^*B)$.
- In uniform-block statements, block sizes are positive and divide the ambient
  dimension. Exact theorem types specify all size and permutation hypotheses.
- Complete-block sharing means equal physical blocks within the same layer.
  Labels and multiplicities may differ between layers. Partial-block ties and
  cross-layer ties are not covered by the shared-group construction.
- Sharing geometry permits arbitrary overlap and fixed matrix carriers,
  including singular carriers. The shared geodesic specialization requires an
  actual permutation and absence of off-diagonal overlap.

## Results corresponding to the paper

| Paper topic | Formalized result | Scope and qualification |
| --- | --- | --- |
| Structured products and shuffles | Concrete matrix products, support predicates, perfect shuffle identities and Kronecker-factor interchange | General rectangular chains of arbitrary depth are not assembled |
| Two-factor block expansion | Exact cell expansion and an if-and-only-if block-rank criterion | Includes singular matrices, empty cells and arbitrary permutations |
| Orthogonalization for two and three factors | Orthogonal products admit orthogonal structured factors with the same permutations | Constructed QR/RQ proofs; an additional partition formulation covers unequal consecutive middle blocks |
| Two-factor smooth geometry | An atlas on the actual orthogonal matrix orbit with inherited topology, smooth inclusion and injective differential | Arbitrary overlap; continuous stabilizers are handled by horizontal slices |
| Tangent projection and AD identities | True tangent-image theorems, Frobenius orthogonal projection, least-squares characterization, differential and adjoint formulas | Mathematical derivatives, not verification of an AD software package |
| Sharing within layers | Compact shared factor groups, actual orbit atlas, local factor sections, canonical projector/lift, metric and gradient | Complete physical blocks; coupled normal equations include physical multiplicities |
| Retractions and descent | Well-defined smooth whole-tangent-bundle Cayley retractions, zero-section and identity-fibre-differential laws, Armijo decrease and finite backtracking | No floating-point or global optimizer convergence guarantee |
| Nonoverlap geodesics | Block exponential curves in the actual matrix orbit through every initial tangent, with zero induced covariant acceleration and constant speed | Includes the exact scalar-shuffle hypothesis `k1 >= b2` and the complete-block sharing extension |
| Three-factor CS special case | Full real square CS decomposition and exact `(p,2,p)` scalar-shuffle exhaustion | Singular-value endpoints and degeneracies are included |
| Three-factor singularities | Full local-neighbourhood model and failure of local Euclidean structure at a specified point | Real `p = 2`, all `q >= 3`; stronger than the odd-cone-width restriction in the paper |
| Four factors | Explicit orthogonal `6 x 6` counterexample to orthogonal-factor sufficiency | Also a denominator-free polynomial obstruction and open exclusion neighbourhood |

See [PAPER_COVERAGE.md](docs/PAPER_COVERAGE.md) for source labels and
[RESULTS.md](docs/RESULTS.md) for exact Lean declarations. The geometry proves
properties of the actual orbit, not only of a formal quotient or factor space.

## Extensions and additional formal results

The following are not claimed to be verbatim formalizations of individual
statements in the paper. Some strengthen its conclusions; others supply details
or general-purpose infrastructure needed for rigorous formal geometry.

1. **Stronger real singularity theorem.** The original `p = 2` orthogonal family
   is not locally Euclidean for every `q >= 3`. The proof does not assume an
   unconstructed sphere-homology profile or a general Hopf--Rinow theorem.
2. **Complex algebra and CS theory.** Structured complex QR/RQ, two- and
   three-factor unitarization, complete unitary CS decomposition, exact shuffle
   exhaustion, and a four-factor counterexample against arbitrary unitary
   factors.
3. **Unitary local topology.** A full `(2,q,2)` neighbourhood model, an embedded
   smoothness obstruction, and genuine topological nonmanifoldness for odd
   `q >= 3`. No even-`q` topological theorem is claimed.
4. **Detailed sharing geometry over both fields.** An inherited-topology atlas,
   actual tangent bridge, smoothly varying physical projector and minimum-norm
   lift, and smooth metric. The unavoidable unitary phase kernel is retained.
5. **Bundled optimization.** Canonical retractions on the actual entire tangent
   bundle, intrinsic gradients as bundle sections, and `C^(r+1)`-to-`C^r`
   regularity. This is stronger than a fixed-factor first-order calculation.
6. **Additional algebraic and differential interfaces.** Rank criteria,
   polynomial obstruction stability, projected derivatives, local connection
   identities, and partial differential components of overlap geodesics.

The special-unitary development in `experimental/special_unitary/` is an
unfinished draft outside the supported build. It imposes determinant one on
each physical block and uses exponential updates.

## What is not formalized

- A complete arbitrary-depth rectangular-word theory, hierarchical flattening
  theorem, general invertible-factor classification, or all singular strata.
- The general rank-one-cone nonmanifold theorem for all row and column sizes.
- General covering-space/Riemannian-covering infrastructure, curvature, shortest
  connecting geodesics, intrinsic distance, and a global bundled Levi-Civita API.
- Complete Lean integration of the arbitrary-overlap three-exponential geodesic
  formula; its written derivation and checked differential components are
  distinguished in [ORTHOGONAL_GEODESICS.md](docs/ORTHOGONAL_GEODESICS.md).
- General unitary shared geodesics, even-`q` unitary topological obstruction,
  cross-layer sharing or partial-block sharing.
- A certified executable coupled solver or global convergence/rate theorem.

## Build and check

Install [elan](https://github.com/leanprover/elan) and Python 3, then run:

```sh
python3 scripts/fetch_cache.py
python3 scripts/verify.py --sequential
```

The project pins Lean **4.19.0** and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The verifier builds the supported
library and checks transitive proof dependencies against `propext`,
`Classical.choice`, and `Quot.sound`. Generated reports remain in the ignored
`.lake/verification/` directory. See [VERIFICATION.md](docs/VERIFICATION.md).

```lean
import GSResults  -- public mathematical results
-- import GSChecked  -- complete supported library
```

Individual modules can be built with, for example:

```sh
lake build GS.UnitarySharing.GradientSection
```

## Repository layout

| Path | Contents |
| --- | --- |
| `GS/` | Matrix algebra, geometry, optimization and topology |
| `GS/Results/`, `GSResults.lean` | Public result interfaces |
| `experimental/special_unitary/` | Unfinished SU development, excluded from the supported build |
| `docs/` | Mathematical guides, paper correspondence and remaining scope |
| `scripts/`, `.github/workflows/` | Reproducible checks and continuous integration |

## License

The project is distributed under the [MIT License](LICENSE).
Reused code retains its applicable MIT or Apache-2.0 notices; see
[THIRD_PARTY.md](docs/THIRD_PARTY.md). The project license does not relicense
the paper or dependencies.
