module

public import GS.Revision.TwoFactorCells
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Rank characterization of independently supported two-factor products

The intermediate slots are partitioned by their left and right block labels.
A matrix admits the prescribed supported factorization exactly when each
output block has rank at most the number of intermediate slots in its cell.

The rank bound is both necessary and sufficient. The converse constructs a
basis factorization of each block and pads it with zeros into the cell slots;
`GS.Revision.Cells.global_iff_independent` then glues these independent factors.
Empty cells and rank-zero matrices are included without separate hypotheses.
-/

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.Results.CellRank

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

/-- A matrix factors through a coordinate space of dimension equal to its rank.
The factors are obtained from a basis of the range of its multiplication map. -/
theorem exists_rank_factorization (A : Matrix ι κ ℝ) :
    ∃ U : Matrix ι (Fin A.rank) ℝ, ∃ V : Matrix (Fin A.rank) κ ℝ, A = U * V := by
  classical
  let S : Submodule ℝ (ι → ℝ) := LinearMap.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) ℝ S := Module.finBasis ℝ S
  let x : κ → S := fun j => A.mulVecLin.rangeRestrict (Pi.single j 1)
  let U : Matrix ι (Fin A.rank) ℝ := fun i k => (b k : ι → ℝ) i
  let V : Matrix (Fin A.rank) κ ℝ := fun k j => b.repr (x j) k
  refine ⟨U, V, ?_⟩
  ext i j
  have h := congrArg (fun y : S => (y : ι → ℝ) i) (b.sum_repr (x j))
  simpa only [U, V, x, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mulVecLin_apply,
    LinearMap.rangeRestrict, LinearMap.codRestrict_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply, mul_comm] using h.symm

/-- Factoring through any finite set of coordinates is equivalent to the rank
bound given by its cardinality. No factorization witness is an assumption. -/
theorem rank_le_card_iff_factorization (A : Matrix ι κ ℝ) :
    A.rank ≤ Fintype.card τ ↔
      ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ, A = U * V := by
  classical
  constructor
  · intro h
    obtain ⟨U, V, hA⟩ := exists_rank_factorization A
    let e : Fin A.rank → τ := fun k => (Fintype.equivFin τ).symm (Fin.castLE h k)
    have he : Function.Injective e :=
      (Fintype.equivFin τ).symm.injective.comp (Fin.castLE_injective h)
    let U' : Matrix ι τ ℝ := fun i => Function.extend e (U i) 0
    let V' : Matrix τ κ ℝ := fun t j => Function.extend e (fun k => V k j) 0 t
    refine ⟨U', V', hA.trans ?_⟩
    ext i j
    apply Fintype.sum_of_injective e he
    · intro t ht
      have ht' : ¬ ∃ k, e k = t := ht
      simp [U', V', Function.extend_apply', ht']
    · intro k
      simp [U', V', he.extend_apply]
  · rintro ⟨U, V, rfl⟩
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

section Cells

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Slots simultaneously belonging to the chosen output row and column blocks. -/
abbrev Cell (left : τ → α) (right : τ → β) (a : α) (b : β) :=
  {t : τ // a = left t ∧ b = right t}

private theorem cellSum_eq_product
    (left : τ → α) (right : τ → β) (a : α) (b : β)
    (U : Matrix ι τ ℝ) (V : Matrix τ κ ℝ) :
    Revision.Cells.cellSum left right a b U V =
      Matrix.of (fun i (t : Cell left right a b) => U i t.val) *
        Matrix.of (fun (t : Cell left right a b) j => V t.val j) := by
  classical
  ext i j
  symm
  apply Fintype.sum_of_injective (Subtype.val : Cell left right a b → τ)
    Subtype.val_injective
  · intro t ht
    have hp : ¬ (a = left t ∧ b = right t) := by
      intro hp
      exact ht ⟨⟨t, hp⟩, rfl⟩
    simp [hp]
  · intro t
    simp [t.property]

/-- A single cell has independent outer-product witnesses exactly when the
corresponding block satisfies its numerical rank bound. -/
theorem cell_factorization_iff_rank
    (left : τ → α) (right : τ → β) (a : α) (b : β) (B : Matrix ι κ ℝ) :
    (∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ,
      B = Revision.Cells.cellSum left right a b U V) ↔
      B.rank ≤ Fintype.card (Cell left right a b) := by
  classical
  constructor
  · rintro ⟨U, V, hB⟩
    apply (rank_le_card_iff_factorization (τ := Cell left right a b) B).mpr
    exact ⟨_, _, hB.trans (cellSum_eq_product left right a b U V)⟩
  · intro h
    obtain ⟨U, V, hB⟩ :=
      (rank_le_card_iff_factorization (τ := Cell left right a b) B).mp h
    let U' : Matrix ι τ ℝ := fun i t =>
      if ht : a = left t ∧ b = right t then U i ⟨t, ht⟩ else 0
    let V' : Matrix τ κ ℝ := fun t j =>
      if ht : a = left t ∧ b = right t then V ⟨t, ht⟩ j else 0
    have hU : Matrix.of (fun i (t : Cell left right a b) => U' i t.val) = U := by
      ext i t
      simp [U', t.property]
    have hV : Matrix.of (fun (t : Cell left right a b) j => V' t.val j) = V := by
      ext t j
      simp [V', t.property]
    refine ⟨U', V', ?_⟩
    rw [cellSum_eq_product, hU, hV]
    exact hB

/-- Complete block-rank characterization of the global supported two-factor
class. Each block rank is bounded by the number of its intermediate slots. -/
theorem global_iff_block_rank
    (left : τ → α) (right : τ → β)
    (A : Matrix (α × ι) (β × κ) ℝ) :
    Revision.Cells.GloballyFactorable left right A ↔
      ∀ a b, (Matrix.of fun i j => A (a, i) (b, j)).rank ≤
        Fintype.card (Cell left right a b) := by
  rw [Revision.Cells.global_iff_independent]
  constructor
  · intro h a b
    obtain ⟨U, V, hUV⟩ := h a b
    apply (cell_factorization_iff_rank left right a b _).mp
    exact ⟨U, V, Matrix.ext hUV⟩
  · intro h a b
    obtain ⟨U, V, hUV⟩ := (cell_factorization_iff_rank left right a b _).mpr (h a b)
    exact ⟨U, V, fun i j => congrArg (fun B : Matrix ι κ ℝ => B i j) hUV⟩

end Cells

end GS.Results.CellRank
