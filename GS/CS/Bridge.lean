module

public import GS.NonmanifoldCompletion.BlockRealization
public import GS.CS.Square

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The square CS decomposition in the original scalar shuffle coordinates

The coordinate changes in this file preserve the original `BlockDiagonal`
predicate and the exact scalar perfect shuffle.
-/

noncomputable section
open Matrix GS.NonmanifoldCompletion
namespace GS.CS

/-- The two large blocks viewed either as a product or as a disjoint sum. -/
def twoProdSumEquiv (p : ℕ) : (Fin 2 × Fin p) ≃ (Fin p ⊕ Fin p) where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := Sum.elim (fun i => (0, i)) (fun i => (1, i)) x
  left_inv := by
    rintro ⟨a, i⟩
    fin_cases a <;> simp
  right_inv := by
    intro x
    cases x <;> simp

/-- Sum-indexed square matrices in the original consecutive scalar order. -/
def squareFlatten {p : ℕ} (A : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ) :
    Mat (2*p) :=
  flattenBlocks (pullMatrix (twoProdSumEquiv p) A)

theorem squareFlatten_mul {p : ℕ}
    (A B : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ) :
    squareFlatten (A*B) = squareFlatten A * squareFlatten B := by
  rw [squareFlatten, pullMatrix_mul, flattenBlocks_mul]
  rfl

theorem squareFlatten_orthogonal {p : ℕ}
    {A : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) ℝ} (hA : Orthogonal A) :
    Orthogonal (squareFlatten A) :=
  pullMatrix_orthogonal _ (pullMatrix_orthogonal _ hA)

theorem squareFlatten_split {p : ℕ} (A B : Mat p) :
    squareFlatten (fromBlocks A 0 0 B) = flattenBlocks (blockMatrix ![A,B]) := by
  apply congrArg flattenBlocks
  ext ⟨a,i⟩ ⟨b,j⟩
  fin_cases a <;> fin_cases b <;>
    simp [pullMatrix, twoProdSumEquiv, blockMatrix]

theorem squareFlatten_split_blockDiagonal {p : ℕ} (A B : Mat p) :
    BlockDiagonal p (squareFlatten (fromBlocks A 0 0 B)) := by
  rw [squareFlatten_split]
  exact flatten_blockDiagonal _

/-- The original shuffle sends the within-block index to the small block label. -/
theorem square_shuffle_block_label {p : ℕ} (i : Fin (2*p)) :
    (scalarShuffle 2 p i).val / 2 = (finProdFinEquiv.symm i).2.val := by
  let x := finProdFinEquiv.symm i
  have hh := flat_block_label (x.2,x.1)
  have hcast {m n : ℕ} (h : m = n) (a : Fin m) :
      (cast (congrArg Fin h) a).val = a.val := by
    cases h
    rfl
  change (cast (congrArg Fin (Nat.mul_comm p 2))
    (finProdFinEquiv (x.2,x.1))).val / 2 = x.2.val
  rw [hcast (Nat.mul_comm p 2)]
  exact hh

theorem shuffled_square_cs_blockDiagonal {p : ℕ} (c s : Fin p → ℝ) :
    BlockDiagonal 2
      (permMatrix (scalarShuffle 2 p) *
        squareFlatten (fromBlocks (diagonal c) (-diagonal s)
          (diagonal s) (diagonal c)) * (permMatrix (scalarShuffle 2 p))ᵀ) := by
  intro i j hij
  let σ := scalarShuffle 2 p
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := square_shuffle_block_label (σ.symm i)
    have hj := square_shuffle_block_label (σ.symm j)
    simp only [σ,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  rw [perm_conjugate_apply]
  change (fromBlocks (diagonal c) (-diagonal s) (diagonal s) (diagonal c))
    (twoProdSumEquiv p x) (twoProdSumEquiv p y) = 0
  rcases x with ⟨a,u⟩
  rcases y with ⟨b,v⟩
  change u ≠ v at hxy
  fin_cases a <;> fin_cases b <;>
    simp [twoProdSumEquiv, Matrix.diagonal_apply, hxy]

/-- A sum-indexed orthogonal CS sandwich is in the original scalar family. -/
theorem scalar_cs_sandwich_mem {p : ℕ}
    (U₁ U₂ V₁ V₂ : Mat p) (c s : Fin p → ℝ)
    (hU : Orthogonal (fromBlocks U₁ 0 0 U₂))
    (hV : Orthogonal (fromBlocks V₁ 0 0 V₂))
    (hK : Orthogonal (fromBlocks (diagonal c) (-diagonal s)
      (diagonal s) (diagonal c))) :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ
      (squareFlatten (fromBlocks U₁ 0 0 U₂ *
        fromBlocks (diagonal c) (-diagonal s) (diagonal s) (diagonal c) *
        fromBlocks V₁ 0 0 V₂)) := by
  let P := permMatrix (scalarShuffle 2 p)
  let L := squareFlatten (fromBlocks U₁ 0 0 U₂)
  let R := squareFlatten (fromBlocks V₁ 0 0 V₂)
  let K := squareFlatten (fromBlocks (diagonal c) (-diagonal s)
    (diagonal s) (diagonal c))
  have hP : Orthogonal P := perm_orthogonal _
  refine ⟨R, P*K*Pᵀ, L, squareFlatten_split_blockDiagonal _ _,
    shuffled_square_cs_blockDiagonal c s, squareFlatten_split_blockDiagonal _ _,
    squareFlatten_orthogonal hV,
    (hP.mul (squareFlatten_orthogonal hK)).mul hP.transpose,
    squareFlatten_orthogonal hU, ?_⟩
  rw [squareFlatten_mul, squareFlatten_mul]
  change L*K*R = L*Pᵀ*(P*K*Pᵀ)*P*R
  symm
  calc
    L*Pᵀ*(P*K*Pᵀ)*P*R = L*(Pᵀ*P)*K*(Pᵀ*P)*R := by
      simp only [Matrix.mul_assoc]
    _ = L*K*R := by rw [hP.1, Matrix.mul_one, Matrix.mul_one]

/-- Transport a scalar matrix to sum coordinates and back without changing it. -/
theorem squareFlatten_unflatten {p : ℕ} (M : Mat (2*p)) :
    squareFlatten (pullMatrix
      ((finProdFinEquiv.symm.trans (twoProdSumEquiv p)).symm) M) = M := by
  ext i j
  let e := finProdFinEquiv.symm.trans (twoProdSumEquiv p)
  change M (e.symm (e i)) (e.symm (e j)) = M i j
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- Three original scalar GS factors of sizes `p, 2, p` exhaust `O(2p)`.
The intervening permutations are the specified scalar perfect shuffle and its
transpose.  No positivity assumption on `p` or singular-value genericity is
required. -/
theorem orthogonal_mem_scalar_three_factor {p : ℕ} {M : Mat (2*p)}
    (hM : Orthogonal M) :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ M := by
  let Q := pullMatrix
    ((finProdFinEquiv.symm.trans (twoProdSumEquiv p)).symm) M
  have hQ : Orthogonal Q := pullMatrix_orthogonal _ hM
  obtain ⟨U₁, U₂, V₁, V₂, c, s, hU₁, hU₂, hV₁, hV₂, hcs, hfactor⟩ :=
    exists_square_cs Q hQ
  have he : squareFlatten Q = M := squareFlatten_unflatten M
  rw [← he, hfactor]
  exact scalar_cs_sandwich_mem U₁ U₂ V₁ V₂ c s
    (split_orthogonal hU₁ hU₂) (split_orthogonal hV₁ hV₂)
    (csMatrix_orthogonal c s (fun i => (hcs i).2.2))

/-- Exact equality with the full orthogonal family in scalar coordinates. -/
theorem inA3Orth_scalar_two_iff {p : ℕ} {M : Mat (2*p)} :
    InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ M ↔ Orthogonal M := by
  constructor
  · intro h
    exact (inA3Orth_implies_inA3_and_orthogonal (perm_orthogonal _)
      (perm_orthogonal _).transpose h).2
  · exact orthogonal_mem_scalar_three_factor

theorem scalar_three_factor_family_eq_orthogonal (p : ℕ) :
    {M : Mat (2*p) | InA3Orth p 2 p (permMatrix (scalarShuffle 2 p))
      (permMatrix (scalarShuffle 2 p))ᵀ M} = {M | Orthogonal M} := by
  ext M
  exact inA3Orth_scalar_two_iff

end GS.CS
