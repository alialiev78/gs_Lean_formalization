module

public import GS.Core
public import Mathlib.Tactic.Choose

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Independent local factorization witnesses and global two-factor gluing

The permutation is absorbed into the two label maps on the intermediate slots.
An intermediate slot belongs to precisely one output block. This file proves
both directions of independent gluing for arbitrary finite index types.

The local characterization here uses a bounded number of outer-product
summands. `GS.Results.CellRank` proves its equivalence with the numerical
criterion `Matrix.rank ≤ card(cell)`, using an actual rank factorization.
No manifold theorem is claimed by this algebraic gluing result.

This module is included in the full build and axiom audit.
-/
noncomputable section
open Matrix
open scoped BigOperators
namespace GS.Revision.Cells

variable {α β ι κ τ : Type*}
variable [Fintype τ] [DecidableEq α] [DecidableEq β]

/-- Global row/column coordinates are pairs: block label, local coordinate.
Different local sizes can be embedded by zero padding; this theorem itself
uses a common row type ι and common column type κ. -/
def LeftSupport (left : τ → α) (L : Matrix (α × ι) τ ℝ) : Prop :=
  ∀ a i t, a ≠ left t → L (a, i) t = 0

def RightSupport (right : τ → β) (R : Matrix τ (β × κ) ℝ) : Prop :=
  ∀ t b j, b ≠ right t → R t (b, j) = 0

def cellSum (left : τ → α) (right : τ → β) (a : α) (b : β)
    (U : Matrix ι τ ℝ) (V : Matrix τ κ ℝ) : Matrix ι κ ℝ :=
  fun i j => ∑ t, if a = left t ∧ b = right t then U i t * V t j else 0

/-- Each output block has its own witnesses; they need not agree between blocks. -/
def IndependentlyFactorable (left : τ → α) (right : τ → β)
    (A : Matrix (α × ι) (β × κ) ℝ) : Prop :=
  ∀ a b, ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ,
    ∀ i j, A (a, i) (b, j) = cellSum left right a b U V i j

def GloballyFactorable (left : τ → α) (right : τ → β)
    (A : Matrix (α × ι) (β × κ) ℝ) : Prop :=
  ∃ L : Matrix (α × ι) τ ℝ, ∃ R : Matrix τ (β × κ) ℝ,
    LeftSupport left L ∧ RightSupport right R ∧ A = L * R

/-- The supported product has exactly the prescribed local outer-product sum. -/
theorem product_block (left : τ → α) (right : τ → β)
    (L : Matrix (α × ι) τ ℝ) (R : Matrix τ (β × κ) ℝ)
    (hL : LeftSupport left L) (hR : RightSupport right R)
    (a : α) (b : β) (i : ι) (j : κ) :
    (L * R) (a, i) (b, j) =
      cellSum left right a b (fun i t => L (a, i) t) (fun t j => R t (b, j)) i j := by
  simp only [Matrix.mul_apply, cellSum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hl : a = left t
  · by_cases hr : b = right t
    · simp [hl, hr]
    · simp [hl, hr, hR t b j hr]
  · simp [hl, hL a i t hl]

def glueLeft (left : τ → α) (right : τ → β)
    (U : α → β → Matrix ι τ ℝ) : Matrix (α × ι) τ ℝ :=
  fun ai t => if ai.1 = left t then U ai.1 (right t) ai.2 t else 0

def glueRight (left : τ → α) (right : τ → β)
    (V : α → β → Matrix τ κ ℝ) : Matrix τ (β × κ) ℝ :=
  fun t bj => if bj.1 = right t then V (left t) bj.1 t bj.2 else 0

theorem glueLeft_supported (left : τ → α) (right : τ → β)
    (U : α → β → Matrix ι τ ℝ) : LeftSupport left (glueLeft left right U) := by
  intro a i t h
  simp [glueLeft, h]

theorem glueRight_supported (left : τ → α) (right : τ → β)
    (V : α → β → Matrix τ κ ℝ) : RightSupport right (glueRight left right V) := by
  intro t b j h
  simp [glueRight, h]

/-- No compatibility hypothesis between different output-block witnesses is needed. -/
theorem glued_product (left : τ → α) (right : τ → β)
    (U : α → β → Matrix ι τ ℝ) (V : α → β → Matrix τ κ ℝ)
    (a : α) (b : β) (i : ι) (j : κ) :
    (glueLeft left right U * glueRight left right V) (a, i) (b, j) =
      cellSum left right a b (U a b) (V a b) i j := by
  simp only [Matrix.mul_apply, cellSum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hl : a = left t <;> by_cases hr : b = right t <;>
    simp [glueLeft, glueRight, hl, hr]

/-- A genuine set-level characterization, not only a forward rank bound. -/
theorem global_iff_independent (left : τ → α) (right : τ → β)
    (A : Matrix (α × ι) (β × κ) ℝ) :
    GloballyFactorable left right A ↔ IndependentlyFactorable left right A := by
  constructor
  · rintro ⟨L, R, hL, hR, rfl⟩ a b
    exact ⟨(fun i t => L (a, i) t), (fun t j => R t (b, j)),
      fun i j => product_block left right L R hL hR a b i j⟩
  · intro h
    classical
    choose U V hUV using h
    refine ⟨glueLeft left right U, glueRight left right V,
      glueLeft_supported left right U, glueRight_supported left right V, ?_⟩
    ext ai bj
    rcases ai with ⟨a, i⟩
    rcases bj with ⟨b, j⟩
    rw [glued_product]
    exact hUV a b i j

end GS.Revision.Cells
