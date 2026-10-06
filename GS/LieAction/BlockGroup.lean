module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Core

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual group of orthogonal block matrices

This construction uses the core matrix definitions and mathlib. The topology below is the ordinary
subspace topology on real matrices. No manifold structure is postulated.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ}

/-- Orthogonal matrices with the manuscript's exact zero pattern. -/
abbrev BlockO (block : Fin n → ℕ) :=
  {A : Mat n // Supported block A ∧ Orthogonal A}

instance blockOGroup (block : Fin n → ℕ) : Group (BlockO block) where
  one := ⟨1, GS.Supported.one, GS.Orthogonal.one⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1,
    A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᵀ, A.property.1.transpose, A.property.2.transpose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1

@[simp] theorem blockO_one_val (block : Fin n → ℕ) :
    ((1 : BlockO block) : Mat n) = 1 := rfl

@[simp] theorem blockO_mul_val {block : Fin n → ℕ} (A B : BlockO block) :
    ((A * B : BlockO block) : Mat n) = (A : Mat n) * (B : Mat n) := rfl

@[simp] theorem blockO_inv_val {block : Fin n → ℕ} (A : BlockO block) :
    ((A⁻¹ : BlockO block) : Mat n) = (A : Mat n)ᵀ := rfl

theorem blockO_supported {block : Fin n → ℕ} (A : BlockO block) :
    Supported block (A : Mat n) := A.property.1

theorem blockO_orthogonal {block : Fin n → ℕ} (A : BlockO block) :
    Orthogonal (A : Mat n) := A.property.2

/-- Matrix multiplication is continuous for the inherited finite-product topology. -/
theorem continuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → Mat n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  simp only [Matrix.mul_apply]
  apply continuous_finset_sum; intro k _
  exact ((continuous_apply k).comp ((continuous_apply i).comp hA)).mul
    ((continuous_apply j).comp ((continuous_apply k).comp hB))

theorem continuous_matrix_transpose {X : Type*} [TopologicalSpace X]
    {A : X → Mat n} (hA : Continuous A) :
    Continuous (fun x => (A x)ᵀ) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (continuous_apply i).comp ((continuous_apply j).comp hA)

instance blockOContinuousMul (block : Fin n → ℕ) :
    ContinuousMul (BlockO block) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact continuous_matrix_product (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)

instance blockOContinuousInv (block : Fin n → ℕ) :
    ContinuousInv (BlockO block) where
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_matrix_transpose continuous_subtype_val

/-- The two verified continuity instances equip the actual block group with
mathlib's topological-group structure. -/
instance blockOTopologicalGroup (block : Fin n → ℕ) :
    IsTopologicalGroup (BlockO block) where

theorem closed_supported (block : Fin n → ℕ) :
    IsClosed {A : Mat n | Supported block A} := by
  simp only [Supported, Set.setOf_forall]
  apply isClosed_iInter; intro i
  apply isClosed_iInter; intro j
  apply isClosed_iInter; intro _
  exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const

theorem closed_orthogonal : IsClosed {A : Mat n | Orthogonal A} := by
  change IsClosed ({A : Mat n | Aᵀ * A = 1} ∩ {A : Mat n | A * Aᵀ = 1})
  exact (isClosed_eq (continuous_matrix_product
      (continuous_matrix_transpose continuous_id) continuous_id) continuous_const).inter
    (isClosed_eq (continuous_matrix_product continuous_id
      (continuous_matrix_transpose continuous_id)) continuous_const)

theorem orthogonal_entry_bound {A : Mat n} (hA : Orthogonal A) (i j : Fin n) :
    |A i j| ≤ 1 := by
  have hg := congrFun (congrFun hA.1 j) j
  have he : (∑ k : Fin n, A k j * A k j) = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hg
  have hs : A i j * A i j ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg (A k j)) (Finset.mem_univ i)
  by_contra hn
  have hp : 0 < (|A i j| - 1) * (|A i j| + 1) := by
    apply mul_pos
    · linarith [lt_of_not_ge hn]
    · positivity
  nlinarith [sq_abs (A i j)]

theorem compact_blockO_set (block : Fin n → ℕ) :
    IsCompact {A : Mat n | Supported block A ∧ Orthogonal A} := by
  have hc : IsClosed {A : Mat n | Supported block A ∧ Orthogonal A} :=
    (closed_supported block).inter closed_orthogonal
  have hs : {A : Fin n → Fin n → ℝ | Supported block A ∧ Orthogonal A} ⊆
      Set.Icc (fun _ _ => (-1 : ℝ)) (fun _ _ => (1 : ℝ)) := by
    intro A hA
    refine ⟨?_, ?_⟩ <;> intro i j
    · exact (abs_le.mp (orthogonal_entry_bound hA.2 i j)).1
    · exact (abs_le.mp (orthogonal_entry_bound hA.2 i j)).2
  exact (isCompact_Icc (α := Fin n → Fin n → ℝ)).of_isClosed_subset hc hs

instance blockOCompactSpace (block : Fin n → ℕ) : CompactSpace (BlockO block) :=
  isCompact_iff_compactSpace.mp (compact_blockO_set block)

/-- The group whose action appears in the manuscript; right factors are
transposed in the action, not in the group's multiplication. -/
abbrev FactorGroup (block₁ block₂ : Fin n → ℕ) := BlockO block₂ × BlockO block₁

end GS.LieAction
