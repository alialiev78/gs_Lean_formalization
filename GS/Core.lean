module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Matrix objects from the manuscript

The mathematical scope is described in docs/PAPER_COVERAGE.md.

The matrices in this file really are finite real matrices. Orthogonality is
expressed by both Gram identities. In particular it is not an abstract tag.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := Aᵀ * A = 1 ∧ A * Aᵀ = 1

namespace Orthogonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℝ}

@[simp] theorem one : Orthogonal (1 : Matrix ι ι ℝ) := by
  constructor <;> simp

theorem transpose (hA : Orthogonal A) : Orthogonal Aᵀ := by
  constructor
  · simpa using hA.2
  · simpa using hA.1

theorem mul (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (A * B) := by
  constructor
  · calc
      (A * B)ᵀ * (A * B) = Bᵀ * (Aᵀ * A) * B := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hA.1]; simpa using hB.1
  · calc
      (A * B) * (A * B)ᵀ = A * (B * Bᵀ) * Aᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB.2]; simpa using hA.2

theorem neg (hA : Orthogonal A) : Orthogonal (-A) := by
  simpa [Orthogonal, Matrix.transpose_neg] using hA

/-- Any square real matrix with one orthogonal Gram identity has both. -/
theorem of_transpose_mul (hA : Aᵀ * A = 1) : Orthogonal A := by
  exact ⟨hA, mul_eq_one_comm.mp hA⟩

theorem of_mul_transpose (hA : A * Aᵀ = 1) : Orthogonal A := by
  exact ⟨mul_eq_one_comm.mp hA, hA⟩

end Orthogonal

/-- Exact zero pattern: entries connecting different block labels vanish. -/
def Supported {ι : Type*} (block : ι → ℕ) (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

/-- Consecutive, equal-size blocks, with the zero-based convention of the paper. -/
def BlockDiagonal {n : ℕ} (b : ℕ) (A : Mat n) : Prop :=
  Supported (fun i : Fin n => i.val / b) A

/-- Block sizes used in theorem statements are nonzero and divide the dimension. -/
structure BlockSpec (n : ℕ) where
  size : ℕ
  count : ℕ
  size_pos : 0 < size
  dimension : count * size = n

namespace Supported
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {block : ι → ℕ} {A B : Matrix ι ι ℝ}

@[simp] theorem zero : Supported block (0 : Matrix ι ι ℝ) := by
  intro i j hij
  rfl

@[simp] theorem one : Supported block (1 : Matrix ι ι ℝ) := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (congrArg block h)
  simp [Matrix.one_apply, hne]

theorem transpose (hA : Supported block A) : Supported block Aᵀ := by
  intro i j hij
  exact hA j i (Ne.symm hij)

theorem add (hA : Supported block A) (hB : Supported block B) :
    Supported block (A + B) := by
  intro i j hij
  change A i j + B i j = 0
  rw [hA i j hij, hB i j hij, add_zero]

theorem neg (hA : Supported block A) : Supported block (-A) := by
  intro i j hij
  change -A i j = 0
  rw [hA i j hij, neg_zero]

theorem smul (a : ℝ) (hA : Supported block A) : Supported block (a • A) := by
  intro i j hij
  change a * A i j = 0
  rw [hA i j hij, mul_zero]

theorem mul (hA : Supported block A) (hB : Supported block B) :
    Supported block (A * B) := by
  intro i j hij
  change (∑ t, A i t * B t j) = 0
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hit : block i = block t
  · have htj : block t ≠ block j := fun h => hij (hit.trans h)
    rw [hB t j htj, mul_zero]
  · rw [hA i t hit, zero_mul]

end Supported

/-- Scalar block entries can be rectangular as in the initial definition. -/
def RectBlockDiagonal {rows cols : ℕ} (br bc : ℕ)
    (A : Matrix (Fin rows) (Fin cols) ℝ) : Prop :=
  ∀ i j, i.val / br ≠ j.val / bc → A i j = 0

/-- The permutation matrix convention is P e_j = e_(sigma j). -/
def permMatrix {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

section Permutations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem mul_perm_apply (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i j : ι) :
    (A * permMatrix σ) i j = A i (σ j) := by
  classical
  simp [Matrix.mul_apply, permMatrix]

@[simp] theorem perm_mul_apply (σ : Equiv.Perm ι) (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * A) i j = A (σ.symm i) j := by
  classical
  rw [Matrix.mul_apply]
  calc
    (∑ k, permMatrix σ i k * A k j) =
        permMatrix σ i (σ.symm i) * A (σ.symm i) j := by
      apply Finset.sum_eq_single (σ.symm i)
      · intro k hk hki
        have hik : i ≠ σ k := by
          intro h
          apply hki
          simpa using (congrArg σ.symm h).symm
        simp [permMatrix, hik]
      · simp
    _ = A (σ.symm i) j := by simp [permMatrix]

@[simp] theorem perm_transpose (σ : Equiv.Perm ι) :
    (permMatrix σ)ᵀ = permMatrix σ.symm := by
  ext i j
  change (if j = σ i then (1 : ℝ) else 0) =
    (if i = σ.symm j then (1 : ℝ) else 0)
  have he : j = σ i ↔ i = σ.symm j := by
    constructor
    · intro h
      simpa using (congrArg σ.symm h).symm
    · intro h
      simpa using (congrArg σ h).symm
  by_cases h : j = σ i
  · rw [if_pos h, if_pos (he.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (he.mpr h'))]

theorem perm_orthogonal (σ : Equiv.Perm ι) : Orthogonal (permMatrix σ) := by
  constructor <;> ext i j <;>
    simp [perm_transpose, perm_mul_apply, permMatrix, Matrix.one_apply]

/-- Conjugation is a simultaneous relabeling, not an arbitrary zeroing operation. -/
theorem perm_conjugate_apply (σ : Equiv.Perm ι) (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * A * (permMatrix σ)ᵀ) i j = A (σ.symm i) (σ.symm j) := by
  simp [perm_transpose]

/-- A permutation transports the block labels together with the zero pattern. -/
theorem supported_perm_conjugate_iff (block : ι → ℕ) (σ : Equiv.Perm ι)
    (A : Matrix ι ι ℝ) :
    Supported (block ∘ σ.symm) (permMatrix σ * A * (permMatrix σ)ᵀ) ↔
      Supported block A := by
  constructor
  · intro h i j hij
    have hz := h (σ i) (σ j) (by simpa using hij)
    simpa using hz
  · intro h i j hij
    simpa using h (σ.symm i) (σ.symm j) hij

end Permutations

/-- A concrete two-factor matrix expression. -/
def product2 {n} (B₂ P B₁ : Mat n) : Mat n := B₂ * P * B₁

def product3 {n} (B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₃ * P₂ * B₂ * P₁ * B₁

def product4 {n} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def InA2 {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ A = product2 B₂ P B₁

def InA2Orth {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ A = product2 B₂ P B₁

def InA3 {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Orth {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def InA4 {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def InA4Orth {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ Orthogonal B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

theorem inA3Orth_implies_inA3_and_orthogonal {n b₁ b₂ b₃}
    {P₁ P₂ A : Mat n} (hP₁ : Orthogonal P₁) (hP₂ : Orthogonal P₂)
    (h : InA3Orth b₁ b₂ b₃ P₁ P₂ A) :
    InA3 b₁ b₂ b₃ P₁ P₂ A ∧ Orthogonal A := by
  rcases h with ⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, hu₁, hu₂, hu₃, rfl⟩
  constructor
  · exact ⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, rfl⟩
  · exact (((hu₃.mul hP₂).mul hu₂).mul hP₁).mul hu₁

/-- General square-depth model; factors are listed from left to right. -/
def InWord {n} (predicates : List (Mat n → Prop)) (A : Mat n) : Prop :=
  ∃ factors : List (Mat n), List.Forall₂ (fun p B => p B) predicates factors ∧ factors.prod = A

end GS
