module

public import GS.UnitarySharing.Factors
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Physical blocks, their determinants, and their infinitesimal traces

Blocks are extracted using an actual ambient row as an anchor. This avoids a
second ambient-dimension equality and works also when the ambient type is empty.
Every physical block is checked; duplicate anchors impose the same condition.
A determinant-one condition on the whole factor is NOT substituted for these
blockwise conditions.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open GS.GlobalGeometry (localBlockIndex localBlockIndex_div localBlockIndex_mod)
open scoped BigOperators Topology
namespace GS.SpecialUnitarySharing
abbrev Pattern := GS.UnitarySharing.Pattern
variable {n : ℕ} {s : Pattern n}

/-- The full physical block containing row `i`, in its local index order. -/
def blockMatrix (s : Pattern n) (i : Fin n) (A : CMat n) : CMat s.size :=
  fun j k => A (localBlockIndex s.positive s.divides i j)
    (localBlockIndex s.positive s.divides i k)

@[simp] theorem blockMatrix_zero (s : Pattern n) (i : Fin n) :
    blockMatrix s i (0 : CMat n) = 0 := rfl
@[simp] theorem blockMatrix_add (s : Pattern n) (i : Fin n) (A B : CMat n) :
    blockMatrix s i (A + B) = blockMatrix s i A + blockMatrix s i B := rfl
@[simp] theorem blockMatrix_sub (s : Pattern n) (i : Fin n) (A B : CMat n) :
    blockMatrix s i (A - B) = blockMatrix s i A - blockMatrix s i B := rfl
@[simp] theorem blockMatrix_neg (s : Pattern n) (i : Fin n) (A : CMat n) :
    blockMatrix s i (-A) = -blockMatrix s i A := rfl
@[simp] theorem blockMatrix_real_smul (s : Pattern n) (i : Fin n) (a : ℝ) (A : CMat n) :
    blockMatrix s i (a • A) = a • blockMatrix s i A := rfl
@[simp] theorem blockMatrix_complex_smul (s : Pattern n) (i : Fin n) (a : ℂ) (A : CMat n) :
    blockMatrix s i (a • A) = a • blockMatrix s i A := rfl
@[simp] theorem blockMatrix_conjTranspose (s : Pattern n) (i : Fin n) (A : CMat n) :
    blockMatrix s i Aᴴ = (blockMatrix s i A)ᴴ := rfl

theorem localIndex_injective (s : Pattern n) (i : Fin n) :
    Function.Injective (localBlockIndex s.positive s.divides i) := by
  intro a b h
  apply Fin.ext
  have he := congrArg (fun j : Fin n => j.val % s.size) h
  simpa only [localBlockIndex_mod] using he

@[simp] theorem blockMatrix_one (s : Pattern n) (i : Fin n) :
    blockMatrix s i (1 : CMat n) = 1 := by
  ext j k
  simp only [blockMatrix, Matrix.one_apply, (localIndex_injective s i).eq_iff]

theorem localIndex_nested (s : Pattern n) (i : Fin n) (j k : Fin s.size) :
    localBlockIndex s.positive s.divides
      (localBlockIndex s.positive s.divides i j) k =
      localBlockIndex s.positive s.divides i k := by
  apply Fin.ext
  change (localBlockIndex s.positive s.divides i j).val / s.size * s.size + k.val =
    i.val / s.size * s.size + k.val
  rw [localBlockIndex_div]

/-- Restriction is multiplicative on the supported algebra, not on all matrices. -/
theorem blockMatrix_mul (s : Pattern n) (i : Fin n) (A B : CMat n)
    (hA : CSupported s.block A) :
    blockMatrix s i (A * B) = blockMatrix s i A * blockMatrix s i B := by
  ext j k
  change (A * B) (localBlockIndex s.positive s.divides i j)
    (localBlockIndex s.positive s.divides i k) =
      ∑ l : Fin s.size, blockMatrix s i A j l * blockMatrix s i B l k
  rw [GS.UnitarySharing.mul_apply_localBlockIndex s.positive s.divides hA]
  apply Finset.sum_congr rfl
  intro l _
  simp only [localIndex_nested, blockMatrix]

def blockMap (s : Pattern n) (i : Fin n) : CMat n →L[ℝ] CMat s.size :=
  ({ toFun := blockMatrix s i
     map_add' := blockMatrix_add s i
     map_smul' := fun a A => blockMatrix_real_smul s i a A
   } : CMat n →ₗ[ℝ] CMat s.size).toContinuousLinearMap

@[simp] theorem blockMap_apply (s : Pattern n) (i : Fin n) (A : CMat n) :
    blockMap s i A = blockMatrix s i A := rfl

theorem blockMatrix_unitary (s : Pattern n) (i : Fin n) (A : CMat n)
    (hAs : CSupported s.block A) (hA : Unitary A) :
    Unitary (blockMatrix s i A) := by
  constructor
  · rw [← blockMatrix_conjTranspose, ← blockMatrix_mul s i Aᴴ A hAs.conjTranspose,
      hA.1, blockMatrix_one]
  · rw [← blockMatrix_conjTranspose, ← blockMatrix_mul s i A Aᴴ hAs,
      hA.2, blockMatrix_one]

theorem blockMatrix_skew (s : Pattern n) (i : Fin n) (A : CMat n)
    (hA : IsSkewHermitian A) : IsSkewHermitian (blockMatrix s i A) := by
  change (blockMatrix s i A)ᴴ = -blockMatrix s i A
  rw [← blockMatrix_conjTranspose, hA, blockMatrix_neg]

/-- Matrices tied by one label have exactly the same extracted physical block. -/
theorem blockMatrix_eq_of_tied (s : Pattern n) (A : CMat n)
    (hA : GS.UnitarySharing.TiedEntries s.size s.label A) (i j : Fin n)
    (hij : s.label (s.block i) = s.label (s.block j)) :
    blockMatrix s i A = blockMatrix s j A := by
  ext a b
  apply hA
  · simp only [localBlockIndex_div]
  · simp only [localBlockIndex_div]
  · simpa only [localBlockIndex_div] using hij
  · simp only [localBlockIndex_mod]
  · simp only [localBlockIndex_mod]

/-- Trace zero in every physical block, not just trace zero in the full matrix. -/
def BlockTraceZero (s : Pattern n) (A : CMat n) : Prop :=
  ∀ i : Fin n, Matrix.trace (blockMatrix s i A) = 0

/-- Determinant one in every physical block, not just in their product. -/
def BlockDetOne (s : Pattern n) (A : CMat n) : Prop :=
  ∀ i : Fin n, Matrix.det (blockMatrix s i A) = 1

theorem blockTraceZero_zero (s : Pattern n) : BlockTraceZero s (0 : CMat n) := by
  intro i
  simp [BlockTraceZero]

theorem blockTraceZero_add (A B : CMat n) (hA : BlockTraceZero s A)
    (hB : BlockTraceZero s B) : BlockTraceZero s (A + B) := by
  intro i
  rw [blockMatrix_add, Matrix.trace_add, hA i, hB i, add_zero]

theorem blockTraceZero_smul (a : ℝ) (A : CMat n) (hA : BlockTraceZero s A) :
    BlockTraceZero s (a • A) := by
  intro i
  rw [blockMatrix_real_smul, Matrix.trace_smul, hA i, smul_zero]

theorem blockDetOne_one (s : Pattern n) : BlockDetOne s (1 : CMat n) := by
  intro i
  rw [blockMatrix_one, Matrix.det_one]

theorem blockDetOne_mul (A B : CMat n) (hAs : CSupported s.block A)
    (hA : BlockDetOne s A) (hB : BlockDetOne s B) : BlockDetOne s (A * B) := by
  intro i
  rw [blockMatrix_mul s i A B hAs, Matrix.det_mul, hA i, hB i, one_mul]

theorem blockDetOne_conjTranspose (A : CMat n) (hA : BlockDetOne s A) :
    BlockDetOne s Aᴴ := by
  intro i
  rw [blockMatrix_conjTranspose, Matrix.det_conjTranspose, hA i, star_one]

theorem isClosed_blockDetOne (s : Pattern n) :
    IsClosed {A : CMat n | BlockDetOne s A} := by
  simp only [BlockDetOne, Set.setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (blockMap s i).continuous.matrix_det continuous_const

end GS.SpecialUnitarySharing
