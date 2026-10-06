# Remaining work

The supported O/U library covers two- and three-factor sufficiency, real and
complex CS decomposition, four-factor counterexamples, two-factor geometry
with arbitrary overlap, complete-block sharing, canonical retractions and
intrinsic gradients. Orthogonal nonoverlap geodesics are proved in the actual
orbit. The real `p = 2` topological obstruction holds for all `q >= 3`; the
unitary topological obstruction holds for odd `q >= 3`.

The table distinguishes missing formal interfaces from broader mathematical
and numerical problems. Difficulty estimates are qualitative.

| Task | Boundary | Estimated difficulty |
| --- | --- | --- |
| Arbitrary-overlap three-exponential geodesics | Written derivation and differential components exist; complete Lean integration remains | Moderate formalization work |
| Global Levi-Civita connection and geodesic flow | Local projected derivatives and metric-compatibility identities exist | Moderate to high |
| Distance, shortest connecting geodesics, cut locus and injectivity radius | Initial-value geodesics do not solve these boundary-value problems | High |
| General shared geodesics and curvature | Complete-block nonoverlap orthogonal case is covered; broader cases are separate | High |
| Partial-block and cross-layer ties | Require appropriate closure and smoothness arguments for the constraint class | High; constraint-dependent |
| General rank-one-cone nonmanifold theorem | Two-row cones and selected three-row widths are covered; arbitrary row/column sizes are not | High |
| Larger-block and arbitrary-depth singularity classification | Existing local models cover the stated `p = 2` families | High |
| Unitary two-factor dimension formula | The skew-Hermitian dimension is proved; assemble the closed combinatorial orbit formula | Low to moderate |
| Independent-atlas unitary gradient-section compatibility | Smooth shared-unitary sections exist; transport to the separate independent atlas is not packaged | Low to moderate |
| Numeric Euclidean dimension in the unitary local-model target | The actual product neighbourhood model is proved; replace its smooth outer factor by explicitly dimensioned coordinates | Low |
| Even-q unitary topological obstruction | Written homological argument exists; the required invariant is not formalized | Substantial topology work |
| General unitary geodesics | Separate from the orthogonal nonoverlap theorem and algebraic phase-gauge identities | Separate extension |
| Hierarchical/rectangular words and invertible factors | Selected definitions and algebraic results exist; full structural theorems are absent | Moderate to high |
| Numerical solvers, rounding error, program cost and convergence rates | Exact maps, least squares and finite backtracking do not establish these guarantees | Substantial implementation and numerical-analysis work |
| Special-unitary sharing | Experimental source outside the supported build; compilation and downstream proof validation remain | Unassessed beyond known compilation failures |

`SphereHomologyProfile` is an explicit unconstructed input to a conditional
homology interface. The final real nonmanifold theorem does not use that
input. Its missing construction does not weaken the unconditional result.

See [PAPER_COVERAGE.md](PAPER_COVERAGE.md) for article coverage,
[ORTHOGONAL_GEODESICS.md](ORTHOGONAL_GEODESICS.md) for the overlap derivation,
and [UNITARY_EVEN_TOPOLOGY.md](UNITARY_EVEN_TOPOLOGY.md) for the unformalized
even-q argument. Mathematical prose in these guides is distinct from a Lean
theorem.
