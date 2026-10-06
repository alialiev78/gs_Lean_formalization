module

public import GS.UnitarySharing.Algebra
public import GS.UnitaryManifold.BlockGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Compact groups of repeated physical unitary blocks

`Pattern` records only the block size, its positivity/divisibility, and the
within-layer sharing labels.  `Factor` is a closed subgroup of the existing
block unitary group, with the inherited matrix topology.  In particular,
no group law or topology is imposed on a parametrized image by fiat.
-/

set_option autoImplicit false

noncomputable section
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.UnitarySharing
variable {n : ℕ}

/-- A valid complete-block layout and arbitrary within-layer sharing labels.
Unused labels are allowed; different layers have independent patterns. -/
structure Pattern (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

namespace Pattern

def block (s : Pattern n) (i : Fin n) : ℕ := i.val / s.size

/-- Actual entry equalities define a subgroup of the already constructed
block unitary group. -/
def subgroup (s : Pattern n) : Subgroup (GS.UnitaryManifold.BlockU s.block) where
  carrier := {A | TiedEntries s.size s.label A.val}
  one_mem' := TiedEntries.one s.size s.label
  mul_mem' := by
    intro A B hA hB
    exact TiedEntries.mul s.positive s.divides A.property.1 B.property.1 hA hB
  inv_mem' := by
    intro A hA
    exact hA.conjTranspose

theorem subgroup_isClosed (s : Pattern n) :
    IsClosed (s.subgroup : Set (GS.UnitaryManifold.BlockU s.block)) :=
  (isClosed_tiedEntries s.size s.label).preimage continuous_subtype_val

end Pattern

abbrev Factor (s : Pattern n) := ↥s.subgroup
abbrev Generator (s : Pattern n) := ↥(sharedSkewSpace (n := n) s.size s.label)

namespace Factor
variable {s : Pattern n}

/-- The original finite matrix, through the two inherited subtypes. -/
def matrix (A : Factor s) : CMat n := A.val.val

@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl
@[simp] theorem matrix_mul (A B : Factor s) : matrix (A * B) = matrix A * matrix B := rfl
@[simp] theorem matrix_inv (A : Factor s) : matrix A⁻¹ = (matrix A)ᴴ := rfl

theorem matrix_shared (A : Factor s) : SharedUnitaryFactor s.size s.label (matrix A) :=
  ⟨A.val.property.1, A.val.property.2, A.property⟩

theorem matrix_unitary (A : Factor s) : Unitary (matrix A) := A.val.property.2

theorem matrix_injective : Function.Injective (matrix : Factor s → CMat n) := by
  intro A B h
  apply Subtype.ext
  exact Subtype.ext h

theorem continuous_matrix : Continuous (matrix : Factor s → CMat n) :=
  continuous_subtype_val.comp continuous_subtype_val

def ofMatrix (A : CMat n) (hA : SharedUnitaryFactor s.size s.label A) : Factor s :=
  ⟨⟨A, hA.1, hA.2.1⟩, hA.2.2⟩

@[simp] theorem matrix_ofMatrix (A : CMat n) (hA : SharedUnitaryFactor s.size s.label A) :
    matrix (ofMatrix A hA) = A := rfl

/-- The nested subgroup topology agrees with the direct matrix-subset topology. -/
def matrixHomeomorph (s : Pattern n) :
    Factor s ≃ₜ {A : CMat n // SharedUnitaryFactor s.size s.label A} where
  toFun A := ⟨matrix A, matrix_shared A⟩
  invFun A := ofMatrix A.val A.property
  left_inv A := by apply matrix_injective; rfl
  right_inv A := by apply Subtype.ext; rfl
  continuous_toFun := continuous_matrix.subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end Factor

instance factorCompactSpace (s : Pattern n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp s.subgroup_isClosed.isCompact

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern n) := Factor left × Factor right

end GS.UnitarySharing
