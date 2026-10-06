module

public import GS.Results.CellRank

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Block-rank criterion for the original two-factor matrix class

`inA2_iff_block_rank` is stated for the actual matrices and permutation in
`GS.InA2`. Its blocks are represented as matrices with zeros outside the
selected row and column blocks. Thus no choice of local row/column numbering
is needed, and unequal final blocks or empty intermediate cells cause no
exception. The criterion includes singular factors and singular outputs.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.Results.OriginalCellRank

section Coordinates

variable {α β ι κ τ : Type*}
variable [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype κ] [Fintype τ]

/-- Add explicit block labels to the row and column coordinates, with zero
entries on every copy whose label disagrees with the original coordinate. -/
def labelledMatrix (row : ι → α) (col : κ → β) (A : Matrix ι κ ℝ) :
    Matrix (α × ι) (β × κ) ℝ :=
  fun ai bj => if ai.1 = row ai.2 ∧ bj.1 = col bj.2 then A ai.2 bj.2 else 0

/-- A factorization of the original matrix with prescribed coordinate support. -/
def CoordinateFactorable (row : ι → α) (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) : Prop :=
  ∃ L : Matrix ι τ ℝ, ∃ R : Matrix τ κ ℝ,
    (∀ i t, row i ≠ left t → L i t = 0) ∧
    (∀ t j, col j ≠ right t → R t j = 0) ∧ A = L * R

theorem coordinate_iff_labelled (row : ι → α) (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) :
    CoordinateFactorable row col left right A ↔
      Revision.Cells.GloballyFactorable left right (labelledMatrix row col A) := by
  classical
  constructor
  · rintro ⟨L, R, hL, hR, hA⟩
    let L' : Matrix (α × ι) τ ℝ := fun ai t =>
      if ai.1 = row ai.2 then L ai.2 t else 0
    let R' : Matrix τ (β × κ) ℝ := fun t bj =>
      if bj.1 = col bj.2 then R t bj.2 else 0
    refine ⟨L', R', ?_, ?_, ?_⟩
    · intro a i t h
      by_cases ha : a = row i
      · simpa [L', ha] using hL i t (fun hi => h (ha.trans hi))
      · simp [L', ha]
    · intro t b j h
      by_cases hb : b = col j
      · simpa [R', hb] using hR t j (fun hj => h (hb.trans hj))
      · simp [R', hb]
    · ext ⟨a, i⟩ ⟨b, j⟩
      by_cases ha : a = row i <;> by_cases hb : b = col j <;>
        simp [labelledMatrix, L', R', ha, hb, hA, Matrix.mul_apply]
  · rintro ⟨L', R', hL', hR', hA⟩
    let L : Matrix ι τ ℝ := fun i t => L' (row i, i) t
    let R : Matrix τ κ ℝ := fun t j => R' t (col j, j)
    refine ⟨L, R, ?_, ?_, ?_⟩
    · intro i t h
      exact hL' (row i) i t h
    · intro t j h
      exact hR' t (col j) j h
    · ext i j
      have h := congrArg (fun B => B (row i, i) (col j, j)) hA
      simpa [labelledMatrix, L, R, Matrix.mul_apply] using h

/-- A support factorization exists exactly when every zero-padded output
block has rank at most the number of available intermediate slots. -/
theorem coordinate_iff_block_rank (row : ι → α) (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) :
    CoordinateFactorable row col left right A ↔
      ∀ a b, (Matrix.of fun i j => if a = row i ∧ b = col j then A i j else 0).rank ≤
        Fintype.card (CellRank.Cell left right a b) := by
  rw [coordinate_iff_labelled, CellRank.global_iff_block_rank]
  rfl

end Coordinates

/-- One original output block, represented without choosing local indices. -/
def block {n : ℕ} (b₁ b₂ : ℕ) (A : Mat n) (a b : ℕ) : Mat n :=
  fun i j => if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0

/-- Slots linking the chosen original output row block to its column block. -/
abbrev Slots {n : ℕ} (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (a b : ℕ) :=
  CellRank.Cell (fun t : Fin n => (σ t).val / b₂) (fun t : Fin n => t.val / b₁) a b

theorem inA2_iff_coordinate {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : Mat n) :
    InA2 b₁ b₂ (permMatrix σ) A ↔
      CoordinateFactorable (fun i : Fin n => i.val / b₂)
        (fun j : Fin n => j.val / b₁)
        (fun t : Fin n => (σ t).val / b₂)
        (fun t : Fin n => t.val / b₁) A := by
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, hA⟩
    refine ⟨B₂ * permMatrix σ, B₁, ?_, ?_, hA⟩
    · intro i t h
      rw [mul_perm_apply]
      exact hb₂ i (σ t) h
    · intro t j h
      exact hb₁ t j h.symm
  · rintro ⟨L, R, hL, hR, hA⟩
    refine ⟨R, L * (permMatrix σ)ᵀ, ?_, ?_, ?_⟩
    · intro i j h
      exact hR i j h.symm
    · intro i j h
      rw [perm_transpose, mul_perm_apply]
      apply hL i (σ.symm j)
      simpa only [Equiv.apply_symm_apply] using h
    · simpa only [product2, Matrix.mul_assoc, (perm_orthogonal σ).1,
        Matrix.one_mul] using hA

/-- Exact rank criterion for `GS.InA2`, with its actual permutation and original
coordinates. There are no factorization hypotheses on the right-hand side. -/
theorem inA2_iff_block_rank {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : Mat n) :
    InA2 b₁ b₂ (permMatrix σ) A ↔
      ∀ a b, (block b₁ b₂ A a b).rank ≤ Fintype.card (Slots b₁ b₂ σ a b) := by
  rw [inA2_iff_coordinate, coordinate_iff_block_rank]
  rfl

end GS.Results.OriginalCellRank
