module

public import GS.NonmanifoldCompletion.SpectralTwo

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The original scalar perfect-shuffle family and its small-block coordinates

All equivalences concern the exact GS.localFamily and GS.scalarShuffle already
present in the project.  This file does not redefine the family by its desired
block formula.  Coordinate relabellings and the block factors are constructed.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.NonmanifoldCompletion

section Relabel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Pull back both matrix indices along an equivalence. -/
def pullMatrix (e : β ≃ α) (A : Matrix α α ℝ) : Matrix β β ℝ :=
  fun i j => A (e i) (e j)

@[simp] theorem pullMatrix_transpose (e : β ≃ α) (A : Matrix α α ℝ) :
    pullMatrix e Aᵀ = (pullMatrix e A)ᵀ := rfl

@[simp] theorem pullMatrix_one (e : β ≃ α) :
    pullMatrix e (1 : Matrix α α ℝ) = 1 := by
  ext i j
  simp [pullMatrix, Matrix.one_apply, e.injective.eq_iff]

theorem pullMatrix_mul (e : β ≃ α) (A B : Matrix α α ℝ) :
    pullMatrix e (A*B) = pullMatrix e A * pullMatrix e B := by
  classical
  ext i j
  change (∑ k : α, A (e i) k * B k (e j)) =
    ∑ k : β, A (e i) (e k) * B (e k) (e j)
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

theorem pullMatrix_orthogonal (e : β ≃ α) {A : Matrix α α ℝ}
    (hA : Orthogonal A) : Orthogonal (pullMatrix e A) := by
  constructor
  · rw [← pullMatrix_transpose, ← pullMatrix_mul, hA.1, pullMatrix_one]
  · rw [← pullMatrix_transpose, ← pullMatrix_mul, hA.2, pullMatrix_one]

end Relabel

/-- Flatten the pair-indexed matrix using the SAME equivalence as originalF. -/
def flattenBlocks {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ) : Mat (k*b) :=
  pullMatrix finProdFinEquiv.symm A

@[simp] theorem flattenBlocks_apply {k b : ℕ}
    (A : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ)
    (i j : Fin k × Fin b) :
    flattenBlocks A (finProdFinEquiv i) (finProdFinEquiv j) = A i j := by
  simp [flattenBlocks,pullMatrix]

theorem flattenBlocks_mul {k b : ℕ}
    (A B : Matrix (Fin k × Fin b) (Fin k × Fin b) ℝ) :
    flattenBlocks (A*B) = flattenBlocks A * flattenBlocks B :=
  pullMatrix_mul _ A B

/-- Blocks are indexed by the quotient in the original BlockDiagonal predicate. -/
theorem flat_block_label {k b : ℕ} (p : Fin k × Fin b) :
    (finProdFinEquiv p).val / b = p.1.val := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
  change (p.2.val + b * p.1.val) / b = p.1.val
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]

theorem flatten_blockDiagonal {k b : ℕ} (B : Fin k → Mat b) :
    BlockDiagonal b (flattenBlocks (blockMatrix B)) := by
  intro i j hij
  let x := finProdFinEquiv.symm i
  let y := finProdFinEquiv.symm j
  have hxy : x.1 ≠ y.1 := by
    intro h
    have hi := flat_block_label x
    have hj := flat_block_label y
    simp only [x,y,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  exact if_neg hxy

@[simp] theorem blockMatrix_transpose {k b : ℕ} (B : Fin k → Mat b) :
    (blockMatrix B)ᵀ = blockMatrix (fun i => (B i)ᵀ) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j
  · subst j; simp [blockMatrix]
  · simp [blockMatrix, h, Ne.symm h]

@[simp] theorem blockMatrix_mul {k b : ℕ} (B C : Fin k → Mat b) :
    blockMatrix B * blockMatrix C = blockMatrix (fun i => B i * C i) := by
  classical
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases h : i=j
  · subst j
    simp [Matrix.mul_apply,blockMatrix,Fintype.sum_prod_type]
  · simp [Matrix.mul_apply,blockMatrix,Fintype.sum_prod_type,h]

@[simp] theorem blockMatrix_one (k b : ℕ) :
    blockMatrix (fun _ : Fin k => (1 : Mat b)) = 1 := by
  ext ⟨i,a⟩ ⟨j,c⟩
  by_cases hi : i=j <;> by_cases ha : a=c <;>
    simp [blockMatrix, Matrix.one_apply, hi, ha]

theorem blockMatrix_orthogonal {k b : ℕ} (B : Fin k → Mat b)
    (hB : ∀ i, Orthogonal (B i)) : Orthogonal (blockMatrix B) := by
  constructor
  · rw [blockMatrix_transpose,blockMatrix_mul]
    have he : (fun i => (B i)ᵀ * B i) = (fun _ => (1 : Mat b)) :=
      funext (fun i => (hB i).1)
    rw [he,blockMatrix_one]
  · rw [blockMatrix_transpose,blockMatrix_mul]
    have he : (fun i => B i * (B i)ᵀ) = (fun _ => (1 : Mat b)) :=
      funext (fun i => (hB i).2)
    rw [he,blockMatrix_one]

/-- The central conjugate, displayed in q-by-q blocks of size two. -/
def centralPair {q : ℕ} (A B : Mat q) :
    Matrix (Fin q × Fin 2) (Fin q × Fin 2) ℝ :=
  fun i j => diagTwo (A i.1 j.1) (B i.1 j.1) i.2 j.2

theorem centralPair_as_blocks {q : ℕ} (A B : Mat q) :
    centralPair A B = pullMatrix (Equiv.prodComm _ _) (blockMatrix ![A,B]) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  fin_cases a <;> fin_cases b <;> simp [centralPair,pullMatrix,blockMatrix,diagTwo]

theorem centralPair_orthogonal {q : ℕ} (A B : Mat q)
    (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (centralPair A B) := by
  rw [centralPair_as_blocks]
  apply pullMatrix_orthogonal
  apply blockMatrix_orthogonal
  intro i
  fin_cases i
  · exact hA
  · exact hB

/-- Scalar middle factor, constructed by conjugation with the specified shuffle. -/
def shuffledMiddle {q : ℕ} (A B : Mat q) : Mat (q*2) :=
  let P := permMatrix (scalarShuffle q 2)
  P * flattenBlocks (centralPair A B) * Pᵀ

/-- The shuffle makes the inner pair coordinate the consecutive block label. -/
theorem shuffle_block_label {q : ℕ} (i : Fin (q*2)) :
    (scalarShuffle q 2 i).val / q = (finProdFinEquiv.symm i).2.val := by
  let p := finProdFinEquiv.symm i
  have hh := flat_block_label (p.2,p.1)
  have hcast {m n : ℕ} (h : m = n) (a : Fin m) :
      (cast (congrArg Fin h) a).val = a.val := by
    cases h
    rfl
  change (cast (congrArg Fin (Nat.mul_comm 2 q))
    (finProdFinEquiv (p.2,p.1))).val / q = p.2.val
  rw [hcast (Nat.mul_comm 2 q)]
  exact hh

theorem shuffledMiddle_blockDiagonal {q : ℕ} (A B : Mat q) :
    BlockDiagonal q (shuffledMiddle A B) := by
  intro i j hij
  let σ := scalarShuffle q 2
  let x := finProdFinEquiv.symm (σ.symm i)
  let y := finProdFinEquiv.symm (σ.symm j)
  have hxy : x.2 ≠ y.2 := by
    intro h
    have hi := shuffle_block_label (σ.symm i)
    have hj := shuffle_block_label (σ.symm j)
    simp only [σ,Equiv.apply_symm_apply] at hi hj
    exact hij (hi.trans ((congrArg Fin.val h).trans hj.symm))
  change (permMatrix σ * flattenBlocks (centralPair A B) * (permMatrix σ)ᵀ) i j = 0
  rw [perm_conjugate_apply]
  change diagTwo (A x.1 y.1) (B x.1 y.1) x.2 y.2 = 0
  have hdiag (a b : Fin 2) (hab : a ≠ b) (s t : ℝ) : diagTwo s t a b = 0 := by
    fin_cases a <;> fin_cases b <;> simp_all [diagTwo]
  exact hdiag x.2 y.2 hxy _ _

theorem small_block_sandwich {q : ℕ} (U V : Fin q → Mat 2) (A B : Mat q)
    (i j : Fin q) (a b : Fin 2) :
    (blockMatrix U * centralPair A B * blockMatrix V) (i,a) (j,b) =
      (U i * diagTwo (A i j) (B i j) * V j) a b := by
  classical
  simp [Matrix.mul_apply, blockMatrix, centralPair, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]

/-- Any orthogonal small-block sandwich is a member of the ORIGINAL family. -/
theorem block_sandwich_mem_localFamily {q : ℕ} (U V : Fin q → Mat 2)
    (A B : Mat q) (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hA : Orthogonal A) (hB : Orthogonal B) :
    flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) ∈ localFamily q := by
  let P := permMatrix (scalarShuffle q 2)
  let C := flattenBlocks (centralPair A B)
  have hP : Orthogonal P := perm_orthogonal _
  have hC : Orthogonal C := pullMatrix_orthogonal _ (centralPair_orthogonal A B hA hB)
  refine ⟨flattenBlocks (blockMatrix V), shuffledMiddle A B,
    flattenBlocks (blockMatrix U), flatten_blockDiagonal V,
    shuffledMiddle_blockDiagonal A B, flatten_blockDiagonal U,
    pullMatrix_orthogonal _ (blockMatrix_orthogonal V hV),
    (hP.mul hC).mul hP.transpose,
    pullMatrix_orthogonal _ (blockMatrix_orthogonal U hU), ?_⟩
  change flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) =
    flattenBlocks (blockMatrix U) * Pᵀ * (P*C*Pᵀ) * P * flattenBlocks (blockMatrix V)
  rw [flattenBlocks_mul,flattenBlocks_mul]
  change flattenBlocks (blockMatrix U) * C * flattenBlocks (blockMatrix V) = _
  symm
  calc
    flattenBlocks (blockMatrix U) * Pᵀ * (P*C*Pᵀ) * P *
        flattenBlocks (blockMatrix V) =
        flattenBlocks (blockMatrix U) * (Pᵀ*P) * C * (Pᵀ*P) *
          flattenBlocks (blockMatrix V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP.1,Matrix.mul_one,Matrix.mul_one]

end GS.NonmanifoldCompletion
