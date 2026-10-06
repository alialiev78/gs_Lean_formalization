# Cosine-sine decomposition and the original GS family

The real square CS theorem factors every orthogonal matrix of size `2p` as

\[
Q=\begin{pmatrix}U_1&0\\0&U_2\end{pmatrix}
\begin{pmatrix}C&-S\\S&C\end{pmatrix}
\begin{pmatrix}V_1&0\\0&V_2\end{pmatrix},
\qquad C=\operatorname{diag}(\cos\theta_i),\quad
S=\operatorname{diag}(\sin\theta_i).
\]

All four outer blocks are orthogonal and `0 ≤ θᵢ ≤ π/2`. The statement includes
zero and repeated singular values, endpoint angles, and `p = 0`; it assumes
neither invertibility of an individual subblock nor generic singular values.
The right factors are named in the orientation displayed above.

## Elementary existence proof

1. **Complete columns with diagonal Gram matrix.** If `AᵀA = diag(dᵢ²)`,
   normalize only columns with `dᵢ ≠ 0`, then extend this orthonormal family to
   a basis. Zero Gram entries force zero columns. This gives `A = U diag(d)`
   without dividing by a zero singular value.
2. **Thin CS decomposition.** From `AᵀA + BᵀB = I`, diagonalize `AᵀA` with an
   orthogonal `V`. The other transformed Gram matrix is `I − diag(λ)`.
   Positivity gives `cᵢ = √λᵢ`, `sᵢ = √(1−λᵢ)`, and `cᵢ²+sᵢ²=1`.
   Apply the column-completion result to both transformed blocks.
3. **Complete the square matrix.** Apply thin CS to the first block column of
   `Q`. Multiplication by the transpose of the canonical CS matrix leaves an
   orthogonal block-upper-triangular matrix with identity upper-left block.
   Orthogonality forces the remaining off-diagonal block to vanish and the
   final diagonal block to be orthogonal.
4. **Recover angles.** Set `θᵢ = arccos(cᵢ)` and use nonnegativity to obtain
   `sin(θᵢ)=sᵢ` and the closed first-quadrant range.

This is an existence proof. It does not certify a floating-point CS routine or
its numerical stability, operation count, or choice of ordered angles.

## Exact scalar-shuffle bridge

The square proof uses `Fin p ⊕ Fin p`. The bridge reindexes it into the original
consecutive scalar coordinates `Fin (2*p)` and proves the middle block support
after the exact `GS.scalarShuffle 2 p` permutation. The resulting statement is

```lean
InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
  (permMatrix (scalarShuffle 2 p))ᵀ M ↔ Orthogonal M
```

Thus this specific three-factor family exhausts `O(2p)`. General three-factor
orthogonalization establishes `(InA3 ... M ∧ Orthogonal M) ↔ InA3Orth ... M`;
it does not by itself establish `InA3 ... M` for every orthogonal matrix.
The CS decomposition and support bridge supply that additional assertion for
the displayed block sizes and permutations.

| Source | Main theorem |
| --- | --- |
| `GS/CS/ColumnGram.lean` | `GS.CS.exists_orthogonal_mul_diagonal` |
| `GS/CS/Thin.lean` | `GS.CS.exists_thin_cs` |
| `GS/CS/Square.lean` | `GS.CS.exists_square_cs` |
| `GS/CS/Angles.lean` | `GS.CS.exists_square_cs_angles` |
| `GS/CS/Bridge.lean` | `GS.CS.inA3Orth_scalar_two_iff`, `GS.CS.scalar_three_factor_family_eq_orthogonal` |
| `GS/Results/CosineSine.lean` | `GS.Results.CosineSine.square`, `scalar_exhaustion`, `scalar_family_eq_orthogonal` |

## References and dependencies

For the classical complete decomposition and computational context, see Brian
D. Sutton, [Computing the complete CS decomposition](https://arxiv.org/abs/0707.1838).
The Lean existence proof above uses the project's pinned mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`:

- [Matrix spectral theorem](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/LinearAlgebra/Matrix/Spectrum.lean):
  `Matrix.IsHermitian.eigenvectorUnitary` and
  `Matrix.IsHermitian.star_mul_self_mul_eq_diagonal`.
- [Orthonormal completion](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Analysis/InnerProductSpace/PiL2.lean):
  `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.


