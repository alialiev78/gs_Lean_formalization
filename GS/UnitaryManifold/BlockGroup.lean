module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Unitary.Support
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The actual group of unitary block matrices

The topology is the ordinary subspace topology on complex matrices.
No manifold structure is assumed.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ}

/-- Unitary matrices with the manuscript's exact zero pattern. -/
abbrev BlockU (block : Fin n → ℕ) :=
  {A : CMat n // CSupported block A ∧ Unitary A}

instance blockUGroup (block : Fin n → ℕ) : Group (BlockU block) where
  one := ⟨1, CSupported.one, GS.Unitary.one⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1,
    A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᴴ, A.property.1.conjTranspose, A.property.2.conjTranspose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1

@[simp] theorem blockU_one_val (block : Fin n → ℕ) :
    ((1 : BlockU block) : CMat n) = 1 := rfl

@[simp] theorem blockU_mul_val {block : Fin n → ℕ} (A B : BlockU block) :
    ((A * B : BlockU block) : CMat n) = (A : CMat n) * (B : CMat n) := rfl

@[simp] theorem blockU_inv_val {block : Fin n → ℕ} (A : BlockU block) :
    ((A⁻¹ : BlockU block) : CMat n) = (A : CMat n)ᴴ := rfl

theorem blockU_supported {block : Fin n → ℕ} (A : BlockU block) :
    CSupported block (A : CMat n) := A.property.1

theorem blockU_unitary {block : Fin n → ℕ} (A : BlockU block) :
    Unitary (A : CMat n) := A.property.2

/-- Matrix multiplication is continuous for the inherited finite-product topology. -/
theorem continuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → CMat n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  simp only [Matrix.mul_apply]
  apply continuous_finset_sum; intro k _
  exact ((continuous_apply k).comp ((continuous_apply i).comp hA)).mul
    ((continuous_apply j).comp ((continuous_apply k).comp hB))

theorem continuous_matrix_conjTranspose {X : Type*} [TopologicalSpace X]
    {A : X → CMat n} (hA : Continuous A) :
    Continuous (fun x => (A x)ᴴ) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact ((continuous_apply i).comp ((continuous_apply j).comp hA)).star

instance blockUContinuousMul (block : Fin n → ℕ) :
    ContinuousMul (BlockU block) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact continuous_matrix_product (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)

instance blockUContinuousInv (block : Fin n → ℕ) :
    ContinuousInv (BlockU block) where
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_matrix_conjTranspose continuous_subtype_val

/-- The two verified continuity instances equip the actual block group with
mathlib's topological-group structure. -/
instance blockUTopologicalGroup (block : Fin n → ℕ) :
    IsTopologicalGroup (BlockU block) where

theorem closed_supported (block : Fin n → ℕ) :
    IsClosed {A : CMat n | CSupported block A} := by
  simp only [CSupported, Set.setOf_forall]
  apply isClosed_iInter; intro i
  apply isClosed_iInter; intro j
  apply isClosed_iInter; intro _
  exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const

theorem closed_unitary : IsClosed {A : CMat n | Unitary A} := by
  change IsClosed ({A : CMat n | Aᴴ * A = 1} ∩ {A : CMat n | A * Aᴴ = 1})
  exact (isClosed_eq (continuous_matrix_product
      (continuous_matrix_conjTranspose continuous_id) continuous_id) continuous_const).inter
    (isClosed_eq (continuous_matrix_product continuous_id
      (continuous_matrix_conjTranspose continuous_id)) continuous_const)

theorem unitary_entry_bound {A : CMat n} (hA : Unitary A) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have hg := congrArg Complex.re (congrFun (congrFun hA.1 j) j)
  have he : (∑ k : Fin n, Complex.normSq (A k j)) = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Complex.re_sum, Complex.mul_re, Complex.normSq_apply] using hg
  have hs : Complex.normSq (A i j) ≤ 1 := by
    rw [← he]
    exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (A k j))
      (Finset.mem_univ i)
  nlinarith [Complex.sq_norm (A i j), norm_nonneg (A i j)]

theorem compact_blockU_set (block : Fin n → ℕ) :
    IsCompact {A : CMat n | CSupported block A ∧ Unitary A} := by
  have hc : IsClosed {A : CMat n | CSupported block A ∧ Unitary A} :=
    (closed_supported block).inter closed_unitary
  have hb : IsCompact {A : CMat n | ∀ i j, A i j ∈ Metric.closedBall (0 : ℂ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ =>
      isCompact_closedBall (0 : ℂ) 1))
  apply hb.of_isClosed_subset hc
  intro A hA i j
  simpa [Metric.mem_closedBall, dist_zero_right] using unitary_entry_bound hA.2 i j

instance blockUCompactSpace (block : Fin n → ℕ) : CompactSpace (BlockU block) :=
  isCompact_iff_compactSpace.mp (compact_blockU_set block)

/-- The group whose action appears in the manuscript; right factors are
conjugate-transposed in the action, not in the group's multiplication. -/
abbrev FactorGroup (block₁ block₂ : Fin n → ℕ) := BlockU block₂ × BlockU block₁

end GS.UnitaryManifold
